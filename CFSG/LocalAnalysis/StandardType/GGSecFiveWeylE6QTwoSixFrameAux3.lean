module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrameAux2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixFrameAux4
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModuleTorus

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]

private theorem centralizer_inv_singleton_eq {G : Type} [Group G] {x : G} :
    Subgroup.centralizer ({x⁻¹} : Set G) = Subgroup.centralizer ({x} : Set G) := by
  ext c
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h2 : x * c = c * x := by
      calc x * c = x * (c * x⁻¹) * x := by group
        _ = x * (x⁻¹ * c) * x := by rw [h]
        _ = c * x := by group
    exact h2.symm
  · intro h
    calc c * x⁻¹ = x⁻¹ * (x * c) * x⁻¹ := by group
      _ = x⁻¹ * (c * x) * x⁻¹ := by rw [h]
      _ = x⁻¹ * c := by group

private theorem mul_inv_comm {G : Type} [Group G] {a b : G} (h : a * b = b * a) :
    a * b⁻¹ = b⁻¹ * a := by
  calc a * b⁻¹ = b⁻¹ * (b * a) * b⁻¹ := by group
    _ = b⁻¹ * (a * b) * b⁻¹ := by rw [h]
    _ = b⁻¹ * a := by group

private theorem isPGroup_torUSix (hK : Nat.card K = 4) :
    IsPGroup 3 (USixTwo.torU K) := by
  obtain ⟨ω, hω⟩ := USixTwo.exists_root_omega hK
  rw [isPGroup_iff_pow_pow_eq_one]
  intro y
  exact ⟨1, Subtype.ext (by
    simpa using congrArg Subtype.val (USixTwo.ModuleProof.torU_pow_three hK hω y))⟩

private theorem not_isCyclic_torUSix (hK : Nat.card K = 4) :
    ¬ IsCyclic (USixTwo.torU K) := by
  intro hcyc
  haveI := hcyc
  obtain ⟨ω, hω⟩ := USixTwo.exists_root_omega hK
  have hdvd : Monoid.exponent ↥(USixTwo.torU K) ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
      USixTwo.ModuleProof.torU_pow_three hK hω g
  rw [IsCyclic.exponent_eq_card, USixTwo.card_torU hK] at hdvd
  have hle : 3 ^ 4 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  norm_num at hle

private theorem exists_noncyclic_pSubgroup_of_quot (hK : Nat.card K = 4) {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : ↥L →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hπ : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hnc : ∃ Q : Subgroup ↥L, IsPGroup 3 Q ∧ ¬ IsCyclic Q := by
    let P : Subgroup ↥L := (USixTwo.torU K).comap π
    have hPmap : P.map π = USixTwo.torU K := by
      rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hπ, top_inf_eq]
    let φ : ↥P →* ↥(USixTwo.torU K) :=
      (π.comp P.subtype).codRestrict (USixTwo.torU K) (by
        intro x
        show π (P.subtype x) ∈ USixTwo.torU K
        rw [← hPmap]
        exact ⟨(x : ↥L), x.2, rfl⟩)
    have hφ : Function.Surjective φ := by
      intro e
      have he : (e : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) ∈ P.map π := by
        rw [hPmap]
        exact e.2
      obtain ⟨p, hp, hpe⟩ := Subgroup.mem_map.mp he
      exact ⟨⟨p, hp⟩, Subtype.ext hpe⟩
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 ↥P))
    have hQtop : ((Sylow.mapSurjective (f := φ) hφ Q : Sylow 3 ↥(USixTwo.torU K)) :
        Subgroup ↥(USixTwo.torU K)) = ⊤ := by
      refine ((Sylow.mapSurjective (f := φ) hφ Q).is_maximal' (Q := ⊤) ?_ le_top).symm
      exact IsPGroup.to_subgroup (isPGroup_torUSix hK) ⊤
    have hQmap : (Q : Subgroup ↥P).map φ = ⊤ := by
      rw [← Sylow.coe_mapSurjective (f := φ) hφ Q]
      exact hQtop
    refine ⟨(Q : Subgroup ↥P).map P.subtype, Q.isPGroup'.map P.subtype, ?_⟩
    intro hScyc
    haveI : IsCyclic ((Q : Subgroup ↥P).map P.subtype) := hScyc
    have hQcyc : IsCyclic ↥Q :=
      isCyclic_of_injective
        (Subgroup.equivMapOfInjective (Q : Subgroup ↥P) P.subtype
          (Subgroup.subtype_injective P)).toMonoidHom
        (Subgroup.equivMapOfInjective (Q : Subgroup ↥P) P.subtype
          (Subgroup.subtype_injective P)).injective
    haveI : IsCyclic ↥Q := hQcyc
    let ψ : ↥Q →* ↥(USixTwo.torU K) := φ.comp (Q : Subgroup ↥P).subtype
    have hψ : Function.Surjective ψ := by
      intro e
      have he : e ∈ (Q : Subgroup ↥P).map φ := by rw [hQmap]; exact Subgroup.mem_top e
      obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp he
      exact ⟨⟨q, hq⟩, hqe⟩
    exact (not_isCyclic_torUSix hK) (isCyclic_of_surjective ψ hψ)
  obtain ⟨Q, hQp, hQnc⟩ := hnc
  refine ⟨Q.map L.subtype, Subgroup.map_subtype_le Q, hQp.map L.subtype, ?_⟩
  intro hcyc
  haveI : IsCyclic (Q.map L.subtype) := hcyc
  exact hQnc (isCyclic_of_injective
    (Subgroup.equivMapOfInjective Q L.subtype (Subgroup.subtype_injective L)).toMonoidHom
    (Subgroup.equivMapOfInjective Q L.subtype (Subgroup.subtype_injective L)).injective)

private theorem e6QTwoSixNormalizesBs {Bs : Subgroup G} {x g : G}
    (hx : x ∈ Bs) (hgB : ∀ y ∈ Bs, g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers x) :
    g ∈ Subgroup.normalizer (Bs : Set G) := by
  have hxBs : Subgroup.zpowers x ≤ Bs := Subgroup.zpowers_le.mpr hx
  have hmap_le : Bs.map (MulAut.conj g).toMonoidHom ≤ Bs := by
    rintro _ ⟨y, hy, rfl⟩
    change g * y * g⁻¹ ∈ Bs
    have h := hxBs (hgB y hy)
    have heq : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
    rw [heq]
    exact Bs.mul_mem h hy
  have hmap_eq : Bs.map (MulAut.conj g).toMonoidHom = Bs := by
    refine Subgroup.eq_of_le_of_card_ge hmap_le ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rwa [Subgroup.mem_normalizer_iff_map_conj_eq]

private theorem e6QTwoSixNormalizesL (hK : Nat.card K = 4) {L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal)
    (hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) → IsCyclic S)
    {g : G} (hgx : g * x * g⁻¹ = x⁻¹) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  classical
  let C := Subgroup.centralizer ({x} : Set G)
  let M := L.map (MulAut.conj g).toMonoidHom
  have hgxinv : g⁻¹ * x * g = x⁻¹ := by
    have h2 : g⁻¹ * x⁻¹ * g = x := by
      have h3 := congrArg (fun t => g⁻¹ * t * g) hgx
      simpa [mul_assoc] using h3.symm
    calc g⁻¹ * x * g = (g⁻¹ * x⁻¹ * g)⁻¹ := by group
      _ = x⁻¹ := by rw [h2]
  have hgx' : g * x⁻¹ * g⁻¹ = x := by
    calc g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      _ = x := by rw [hgx, inv_inv]
  have hgC : g ∈ Subgroup.normalizer (C : Set G) := by
    have himage : (MulAut.conj g).toMonoidHom '' ({x} : Set G) = ({x⁻¹} : Set G) := by
      rw [Set.image_singleton]
      show ({g * x * g⁻¹} : Set G) = {x⁻¹}
      rw [hgx]
    have hle := Subgroup.map_centralizer_le_centralizer_image ({x} : Set G)
      (MulAut.conj g).toMonoidHom
    rw [himage, centralizer_inv_singleton_eq] at hle
    have hmap_eq : C.map (MulAut.conj g).toMonoidHom = C := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    rwa [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hCN : C ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLx).mp hN
  have hMleC : M ≤ C := by
    rintro _ ⟨l, hl, rfl⟩
    change g * l * g⁻¹ ∈ C
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hlx : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
    have hlxinv : l * x⁻¹ = x⁻¹ * l := mul_inv_comm hlx
    calc (g * l * g⁻¹) * x = g * l * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * (l * x⁻¹) * g⁻¹ := by rw [hgxinv]; simp only [mul_assoc]
      _ = g * (x⁻¹ * l) * g⁻¹ := by rw [hlxinv]
      _ = (g * x⁻¹ * g⁻¹) * (g * l * g⁻¹) := by group
      _ = x * (g * l * g⁻¹) := by rw [hgx']
  have hMnorm : (M.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hMleC]
    intro m c hm hc
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hm
    have hgCinv : g⁻¹ ∈ Subgroup.normalizer (C : Set G) := Subgroup.inv_mem _ hgC
    have hgcC : g⁻¹ * c * g ∈ C := by
      simpa using (Subgroup.mem_normalizer_iff.mp hgCinv c).mp hc
    have hlL : (g⁻¹ * c * g) * l * (g⁻¹ * c * g)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hCN hgcC) l).mp hl
    refine Subgroup.mem_map.mpr ⟨(g⁻¹ * c * g) * l * (g⁻¹ * c * g)⁻¹, hlL, ?_⟩
    show g * ((g⁻¹ * c * g) * l * (g⁻¹ * c * g)⁻¹) * g⁻¹ = c * (g * l * g⁻¹) * c⁻¹
    group
  let q : ↥L →* (↥L ⧸ Subgroup.center ↥L) := QuotientGroup.mk' (Subgroup.center ↥L)
  let S : Subgroup ↥L := (L ⊓ M).subgroupOf L
  have hSnorm : S.Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    refine ⟨L.mul_mem (L.mul_mem hk hh.1) (L.inv_mem hk), ?_⟩
    exact (Subgroup.normal_subgroupOf_iff hMleC).mp hMnorm h k hh.2 (hLx hk)
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := by
    have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 hK' 6
        (by norm_num) (by norm_num)
    exact θ.isSimpleGroup
  have htopmap : (⊤ : Subgroup ↥L).map L.subtype = L := by
    have := Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) L
    simpa using this
  have hLL : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator L, hperf, htopmap]
  have hLeqM : L = M := by
    haveI hSqnorm : (S.map q).Normal := hSnorm.map q (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.map q) with hbot | htop
    · exfalso
      have hinf_le_center : L ⊓ M ≤ (Subgroup.center ↥L).map L.subtype := by
        intro y hy
        have hyS : (⟨y, hy.1⟩ : ↥L) ∈ S := Subgroup.mem_subgroupOf.mpr hy
        have hq1 : q ⟨y, hy.1⟩ = 1 := by
          have hmem : q ⟨y, hy.1⟩ ∈ S.map q :=
            Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩, hyS, rfl⟩
          rw [hbot] at hmem
          exact Subgroup.mem_bot.mp hmem
        refine Subgroup.mem_map.mpr ⟨⟨y, hy.1⟩, ?_, rfl⟩
        rw [← QuotientGroup.ker_mk' (Subgroup.center ↥L), MonoidHom.mem_ker]
        exact hq1
      have hcomm_le_inf : ⁅L, M⁆ ≤ L ⊓ M := by
        refine le_inf ?_ ?_
        · rw [Subgroup.commutator_le]
          intro l hl m hm
          have hmL : m * l⁻¹ * m⁻¹ ∈ L :=
            (Subgroup.mem_normalizer_iff.mp (hCN (hMleC hm)) l⁻¹).mp (L.inv_mem hl)
          have heq : ⁅l, m⁆ = l * (m * l⁻¹ * m⁻¹) := by
            rw [commutatorElement_def]; group
          rw [heq]
          exact L.mul_mem hl hmL
        · rw [Subgroup.commutator_le]
          intro l hl m hm
          have hlM : l * m * l⁻¹ ∈ M :=
            (Subgroup.normal_subgroupOf_iff hMleC).mp hMnorm m l hm (hLx hl)
          have heq : ⁅l, m⁆ = (l * m * l⁻¹) * m⁻¹ := by
            rw [commutatorElement_def]
          rw [heq]
          exact M.mul_mem hlM (M.inv_mem hm)
      have hcomm_le_Z : ⁅L, M⁆ ≤ (Subgroup.center ↥L).map L.subtype :=
        hcomm_le_inf.trans hinf_le_center
      have hZleCent : (Subgroup.center ↥L).map L.subtype ≤
          Subgroup.centralizer (L : Set G) := by
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
        have hzc := Subgroup.mem_center_iff.mp hc ⟨l, hl⟩
        have hval := congrArg (fun x : ↥L => (x : G)) hzc
        simp only [Subgroup.coe_mul] at hval
        exact hval
      have hZL : ⁅(Subgroup.center ↥L).map L.subtype, L⁆ = ⊥ :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hZleCent
      have h1 : ⁅⁅L, M⁆, L⁆ = ⊥ :=
        le_bot_iff.mp ((Subgroup.commutator_mono hcomm_le_Z le_rfl).trans (le_of_eq hZL))
      have h2 : ⁅⁅M, L⁆, L⁆ = ⊥ := by
        rw [Subgroup.commutator_comm M L]
        exact h1
      have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := L) (H₂ := L) (H₃ := M)
        h1 h2
      rw [hLL] at h3
      have hMleC' : M ≤ Subgroup.centralizer (L : Set G) := by
        have h3' : ⁅M, L⁆ = ⊥ := by
          rw [Subgroup.commutator_comm M L]
          exact h3
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h3'
      obtain ⟨S0, hS0L, hS03, hS0nc⟩ := exists_noncyclic_pSubgroup_of_quot hK θ
      have hS0map : S0.map (MulAut.conj g).toMonoidHom ≤
          Subgroup.centralizer (L : Set G) :=
        (Subgroup.map_mono hS0L).trans hMleC'
      have hcyc' := hcyc (S0.map (MulAut.conj g).toMonoidHom) (hS03.map _) hS0map
      exact hS0nc (isCyclic_of_surjective
        (S0.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
        (MulEquiv.surjective _))
    · have htop_le : (⊤ : Subgroup ↥L) ≤ S ⊔ Subgroup.center ↥L := by
        intro l hl
        have hmem : q l ∈ S.map q := by rw [htop]; exact Subgroup.mem_top _
        obtain ⟨s, hsS, hqs⟩ := Subgroup.mem_map.mp hmem
        have hz : s⁻¹ * l ∈ Subgroup.center ↥L := by
          rw [← QuotientGroup.ker_mk' (Subgroup.center ↥L), MonoidHom.mem_ker]
          rw [map_mul, map_inv, hqs, inv_mul_cancel]
        have heq : l = s * (s⁻¹ * l) := by group
        rw [heq]
        exact Subgroup.mul_mem_sup hsS hz
      have hcomm_le : ⁅S ⊔ Subgroup.center ↥L, S ⊔ Subgroup.center ↥L⁆ ≤ S := by
        have hSZ : ⁅S, Subgroup.center ↥L⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.centralizer_center]
          exact le_top
        have hZS : ⁅Subgroup.center ↥L, S⁆ = ⊥ := by
          rw [Subgroup.commutator_comm]
          exact hSZ
        have hZZ : ⁅Subgroup.center ↥L, Subgroup.center ↥L⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.centralizer_center]
          exact le_top
        rw [Subgroup.commutator_sup_right, Subgroup.commutator_sup_left,
          Subgroup.commutator_sup_left]
        exact sup_le (sup_le (Subgroup.commutator_le_self S) (by rw [hSZ]; exact bot_le))
          (sup_le (by rw [hZS]; exact bot_le) (by rw [hZZ]; exact bot_le))
      have htop_le' : (⊤ : Subgroup ↥L) ≤ S := by
        calc (⊤ : Subgroup ↥L) = ⁅(⊤ : Subgroup ↥L), ⊤⁆ := hperf.symm
          _ ≤ ⁅S ⊔ Subgroup.center ↥L, S ⊔ Subgroup.center ↥L⁆ :=
              Subgroup.commutator_mono htop_le htop_le
          _ ≤ S := hcomm_le
      have hStop : S = ⊤ := top_unique htop_le'
      have hLleM : L ≤ M := by
        intro l hl
        have : (⟨l, hl⟩ : ↥L) ∈ S := by rw [hStop]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).2
      refine Subgroup.eq_of_le_of_card_ge hLleM ?_
      rw [show M = L.map (MulAut.conj g).toMonoidHom from rfl,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact hLeqM.symm

private theorem e6QTwoSixConjPowOdd {x g : G} (hgx : g * x * g⁻¹ = x⁻¹)
    {j : ℕ} (hj : Odd j) : g ^ j * x * (g ^ j)⁻¹ = x⁻¹ := by
  obtain ⟨m, rfl⟩ := hj
  have hg2 : g ^ 2 * x * (g ^ 2)⁻¹ = x := by
    calc g ^ 2 * x * (g ^ 2)⁻¹ = g * (g * x * g⁻¹) * g⁻¹ := by rw [pow_two]; group
      _ = g * x⁻¹ * g⁻¹ := by rw [hgx]
      _ = (g * x * g⁻¹)⁻¹ := by group
      _ = x := by rw [hgx, inv_inv]
  have hg2m : (g ^ 2) ^ m * x * ((g ^ 2) ^ m)⁻¹ = x := by
    induction m with
    | zero => simp
    | succ k ih =>
      calc (g ^ 2) ^ (k + 1) * x * ((g ^ 2) ^ (k + 1))⁻¹
          = g ^ 2 * ((g ^ 2) ^ k * x * ((g ^ 2) ^ k)⁻¹) * (g ^ 2)⁻¹ := by group
        _ = g ^ 2 * x * (g ^ 2)⁻¹ := by rw [ih]
        _ = x := hg2
  have hpow : g ^ (2 * m + 1) = g * (g ^ 2) ^ m := by
    rw [pow_succ', pow_mul]
  calc g ^ (2 * m + 1) * x * (g ^ (2 * m + 1))⁻¹
      = g * ((g ^ 2) ^ m * x * ((g ^ 2) ^ m)⁻¹) * g⁻¹ := by rw [hpow]; group
    _ = g * x * g⁻¹ := by rw [hg2m]
    _ = x⁻¹ := hgx

private theorem e6QTwoSixOddPart (hK : Nat.card K = 4) {Bs L : Subgroup G} {x g : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (hgBs : g ∈ Subgroup.normalizer (Bs : Set G))
    (hgB : ∀ y ∈ Bs, g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers x)
    (hgx : g * x * g⁻¹ = x⁻¹) :
    ∃ g₂ : G, g₂ ∈ Subgroup.centralizer (L : Set G) ∧ g₂ * x * g₂⁻¹ = x⁻¹ := by
  classical
  let N := Subgroup.normalizer (L : Set G)
  let βN := e6QTwoSixFrameAction (le_rfl : N ≤ N) θ
  let γ := βN ⟨g, hgN⟩
  obtain ⟨a, j, hjodd, hord⟩ :=
    Nat.exists_eq_two_pow_mul_odd (n := orderOf g) (orderOf_pos g).ne'
  let g₂ := g ^ j
  have hg2N : g₂ ∈ N := Subgroup.pow_mem _ hgN j
  have hg2pow : g₂ ^ 2 ^ a = 1 := by
    rw [show g₂ ^ 2 ^ a = g ^ (j * 2 ^ a) from by
      dsimp only [g₂]
      rw [← pow_mul]]
    rw [mul_comm j (2 ^ a), ← hord, pow_orderOf_eq_one]
  have hg2inv : g₂ * x * g₂⁻¹ = x⁻¹ := e6QTwoSixConjPowOdd hgx hjodd
  have hγ3 : γ ^ 3 = 1 :=
    e6QTwoSixGamma3 hK θ hperf hBs hcard hx hBL hNL hI hgN hgBs hgB
  have hγj : γ ^ j = βN ⟨g₂, hg2N⟩ := by
    rw [show γ = βN ⟨g, hgN⟩ from rfl, ← map_pow]
    congr 1
  have hγj3 : (γ ^ j) ^ 3 = 1 := by
    calc (γ ^ j) ^ 3 = γ ^ (j * 3) := (pow_mul ..).symm
      _ = γ ^ (3 * j) := by rw [show j * 3 = 3 * j by omega]
      _ = (γ ^ 3) ^ j := pow_mul ..
      _ = 1 := by rw [hγ3, one_pow]
  have hγj2 : (γ ^ j) ^ 2 ^ a = 1 := by
    rw [hγj, ← map_pow]
    have hpow : (⟨g₂, hg2N⟩ : N) ^ 2 ^ a = 1 := by
      apply Subtype.ext
      exact hg2pow
    rw [hpow, map_one]
  have hγj1 : γ ^ j = 1 := e6QTwoEqOneOfPowThreeOfPowTwo hγj3 hγj2
  have hg2C : g₂ ∈ Subgroup.centralizer (L : Set G) := by
    have hker : (⟨g₂, hg2N⟩ : N) ∈ βN.ker := by
      rw [MonoidHom.mem_ker, ← hγj]
      exact hγj1
    rw [e6QTwoSixFrameAction_ker (le_rfl : N ≤ N) θ hperf] at hker
    exact (Subgroup.mem_subgroupOf.mp hker).2
  exact ⟨g₂, hg2C, hg2inv⟩

theorem e6QTwoSixNotMemOfConjEqInv (hK : Nat.card K = 4) {Bs L : Subgroup G} {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    (hx : x ∈ Bs) (hx1 : x ≠ 1)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : ∀ b ∈ Bs, ∃ ψ ∈ LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) ψ)
    (hLx : L ≤ Subgroup.centralizer {x})
    (hN : (L.subgroupOf (Subgroup.centralizer {x})).Normal)
    (hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) → IsCyclic S)
    {g : G} (hgx : g * x * g⁻¹ = x⁻¹)
    (hgB : ∀ y ∈ Bs, g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers x) :
    x ∉ L := by
  have hgBs : g ∈ Subgroup.normalizer (Bs : Set G) := e6QTwoSixNormalizesBs hx hgB
  have hgN : g ∈ Subgroup.normalizer (L : Set G) :=
    e6QTwoSixNormalizesL hK θ hperf hLx hN hcyc hgx
  obtain ⟨g₂, hg2C, hg2inv⟩ :=
    e6QTwoSixOddPart hK θ hperf hBs hcard hx hBL hNL hI hgN hgBs hgB hgx
  intro hxL
  have hcomm : x * g₂ = g₂ * x := Subgroup.mem_centralizer_iff.mp hg2C x hxL
  have hfix : g₂ * x * g₂⁻¹ = x := by
    calc g₂ * x * g₂⁻¹ = x * g₂ * g₂⁻¹ := by rw [hcomm]
      _ = x := by group
  have hxinv : x = x⁻¹ := hfix.symm.trans hg2inv
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hxinv]
    exact mul_inv_cancel x
  have hx3 : x ^ 3 = 1 := hBs.2 x hx
  exact hx1 (e6QTwoEqOneOfPowThreeOfPowTwo (k := 1) hx3 (by simpa using hx2))

end CFSG.StandardType.E6QTwo

end
