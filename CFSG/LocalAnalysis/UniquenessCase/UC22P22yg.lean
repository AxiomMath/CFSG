module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yf
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped commutatorElement

namespace P22y

theorem layer_eq_rankThreeLayer_top (X : Type) [Group X] :
    CFSG.layer X = rankThreeLayer (⊤ : Subgroup X) := by
  rw [CFSG.layer.eq_sSup]
  unfold rankThreeLayer
  congr 1
  ext L
  exact CFSG.isComponent_iff_open L

theorem isQuasisimple_of_isSimpleGroup {X : Type} [Group X] [IsSimpleGroup X]
    (hZ : Subgroup.center X = ⊥) : CFSG.Open.IsQuasisimple X := by
  refine ⟨?_, ?_⟩
  · rcases (inferInstance : (commutator X).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      have hc : Subgroup.center X = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        have hm : ⁅y, x⁆ ∈ commutator X :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x)
        rw [h, Subgroup.mem_bot] at hm
        exact commutatorElement_eq_one_iff_mul_comm.1 hm
      rw [hZ] at hc
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial X)
      have ha : a ∈ (⊥ : Subgroup X) := hc ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup X) := hc ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot] at ha hb
      exact hab (ha.trans hb.symm)
    · exact h
  · have e : X ⧸ Subgroup.center X ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    haveI : Nontrivial (X ⧸ Subgroup.center X) := e.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem isSimpleGroup_of_isL2Ev {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) (hn : 2 ≤ n) :
    IsSimpleGroup X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI := charP_two_of_card hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI := isSimpleGroup_sl2 h4
  let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  haveI : Nontrivial X := e'.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e'.symm.toMonoidHom e'.symm.surjective

theorem three_dvd_card_of_isL2Ev {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) : 3 ∣ Nat.card X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF, ← pow_mul, mul_comm n 2,
    pow_mul]
  have h3 : 4 - 1 ∣ 4 ^ n - 1 ^ n := Nat.sub_dvd_pow_sub_pow 4 1 n
  norm_num at h3
  exact h3.mul_left _

theorem two_le_of_isL2Ev_of_card {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) (h6 : 6 < Nat.card X) :
    2 ≤ n := by
  obtain ⟨F, i1, i2, hF, he⟩ := h
  have hn1 := one_le_of_card hF
  by_contra hn
  have hn' : n = 1 := by omega
  subst hn'
  have := card_of_isL2Ev_one ⟨F, i1, i2, hF, he⟩
  omega

theorem iSupIndep_map {A B : Type} [Group A] [Group B] {ι : Type} {T : ι → Subgroup A} (hT : iSupIndep T)
    (f : A →* B) (hf : Function.Injective f) : iSupIndep fun i => (T i).map f := by
  intro i
  have h : (⨆ (j) (_ : j ≠ i), (T j).map f) = (⨆ (j) (_ : j ≠ i), T j).map f := by
    simp only [Subgroup.map_iSup]
  rw [h]
  exact Subgroup.disjoint_map hf (hT i)

theorem iSup_le_normalizer_of_comm {A : Type} [Group A] {ι : Type} {T : ι → Subgroup A}
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ T i, ∀ y ∈ T j, x * y = y * x) (i : ι) :
    (⨆ j, T j) ≤ normalizer (T i : Set A) := by
  refine iSup_le fun j => ?_
  by_cases h : j = i
  · subst h
    exact Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm i j (Ne.symm h) x hx y hy

theorem rankThreeLayer_iSup_of_comm {A : Type} [Group A] {ι : Type} {T : ι → Subgroup A}
    (hq : ∀ i, CFSG.Open.IsQuasisimple ↥(T i))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ T i, ∀ y ∈ T j, x * y = y * x) :
    rankThreeLayer (⨆ i, T i) = ⨆ i, T i := by
  refine le_antisymm (sSup_le fun L hL => hL.1) (iSup_le fun i => ?_)
  have hle : T i ≤ ⨆ j, T j := le_iSup T i
  exact le_sSup ⟨hle, CFSG.Open.IsSubnormal.step hle
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 (iSup_le_normalizer_of_comm hcomm i))
    (CFSG.Open.IsSubnormal.refl _), hq i⟩

theorem iSup_inf_centralizer_eq_bot {A : Type} [Group A] [Finite A] {ι : Type} [Fintype ι] [DecidableEq ι]
    {T : ι → Subgroup A} (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ T i → y ∈ T j → Commute x y)
    (hind : iSupIndep T) (hZ : ∀ i, Subgroup.center ↥(T i) = ⊥) :
    (⨆ i, T i) ⊓ centralizer ((⨆ i, T i : Subgroup A) : Set A) = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzX, hzC⟩
  rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm)] at hzX
  obtain ⟨w, rfl⟩ := hzX
  have hinj := Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hind
  have hw : w = 1 := by
    funext i
    have hc : w i ∈ Subgroup.center ↥(T i) := by
      rw [Subgroup.mem_center_iff]
      intro n
      have h1 := Subgroup.mem_centralizer_iff.1 hzC (n : A) (Subgroup.mem_iSup_of_mem i n.2)
      have h2 : Subgroup.noncommPiCoprod hcomm (Pi.mulSingle i n * w) =
          Subgroup.noncommPiCoprod hcomm (w * Pi.mulSingle i n) := by
        rw [map_mul, map_mul, Subgroup.noncommPiCoprod_mulSingle]
        exact h1
      have h3 := congrFun (hinj h2) i
      simpa using h3
    rw [hZ i, Subgroup.mem_bot] at hc
    exact hc
  rw [hw, map_one, Subgroup.mem_bot]

theorem eq_bot_of_isPGroup_two {A : Type} [Group A] [Finite A] {ι : Type} [Fintype ι] [DecidableEq ι]
    {T : ι → Subgroup A} (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ T i → y ∈ T j → Commute x y)
    (hind : iSupIndep T) (hS : ∀ i, IsSimpleGroup ↥(T i)) (h3 : ∀ i, 3 ∣ Nat.card ↥(T i))
    (hZ : ∀ i, Subgroup.center ↥(T i) = ⊥) {B : Subgroup A} (hB2 : IsPGroup 2 ↥B)
    (hBX : B ≤ ⨆ i, T i) (hnorm : (⨆ i, T i) ≤ normalizer (B : Set A)) : B = ⊥ := by
  have hcomm' : ∀ i j, i ≠ j → ∀ x ∈ T i, ∀ y ∈ T j, x * y = y * x :=
    fun i j hij x hx y hy => hcomm hij x y hx hy
  have hTn : ∀ i, (⨆ j, T j) ≤ normalizer (T i : Set A) := iSup_le_normalizer_of_comm hcomm'
  have hinf : ∀ i, B ⊓ T i = ⊥ := by
    intro i
    have hn : ((B ⊓ T i).subgroupOf (T i)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact and_congr (Subgroup.mem_normalizer_iff.1 (hnorm (le_iSup T i ht)) x)
        (Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ht) x)
    haveI := hS i
    rcases hn.eq_bot_or_eq_top with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxs : (⟨x, hx.2⟩ : ↥(T i)) ∈ (B ⊓ T i).subgroupOf (T i) := hx
      rw [h, Subgroup.mem_bot] at hxs
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hxs
    · exfalso
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 (h3 i)
      have haB : (a : A) ∈ B := by
        have : a ∈ (B ⊓ T i).subgroupOf (T i) := h ▸ Subgroup.mem_top a
        exact this.1
      obtain ⟨k, hk⟩ := hB2 ⟨a, haB⟩
      have h1 : orderOf (⟨(a : A), haB⟩ : ↥B) = 3 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, ha]
      have h2 : orderOf (⟨(a : A), haB⟩ : ↥B) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      rw [h1] at h2
      have := Nat.prime_three.dvd_of_dvd_pow h2
      omega
  have hcen : B ≤ centralizer ((⨆ i, T i : Subgroup A) : Set A) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    induction hx using Subgroup.iSup_induction' with
    | hp i t ht =>
      have hbt : ⁅t, b⁆ ∈ B ⊓ T i := by
        refine ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          exact B.mul_mem ((Subgroup.mem_normalizer_iff.1 (hnorm (le_iSup T i ht)) b).1 hb) (B.inv_mem hb)
        · have e : ⁅t, b⁆ = t * (b * t⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
          rw [e]
          exact (T i).mul_mem ht ((Subgroup.mem_normalizer_iff.1 (hTn i (hBX hb)) t⁻¹).1 ((T i).inv_mem ht))
      rw [hinf i, Subgroup.mem_bot] at hbt
      exact commutatorElement_eq_one_iff_mul_comm.1 hbt
    | h1 => simp
    | hmul x y _ _ hx hy =>
      rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
  have hle : B ≤ (⨆ i, T i) ⊓ centralizer ((⨆ i, T i : Subgroup A) : Set A) := le_inf hBX hcen
  rwa [iSup_inf_centralizer_eq_bot hcomm hind hZ, le_bot_iff] at hle

end P22y

open P22y

variable {G : Type} [Group G] [Finite G]

theorem uc22p22yg_three_lt_pRank (D : Data G) (Ch : Choice2011 G) (h51 : S22_5_1 D Ch) (h119 : R119W D)
    (hW : InCalW D.M D.T D.U) (hH : H1930 D) (c : Ctx22c D Ch) (m : ℕ)
    (Nb : Fin m → Subgroup (MBar D.M D.U)) (hNb : NbarSplit D Nb) (S : Finset (Fin m))
    (hS4 : 4 ≤ S.card) (hS6 : ∀ k ∈ S, 6 < Nat.card (Nb k)) : 3 < CFSG.Open.pRank 3 D.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcl := h51 hH c m Nb hNb
  have hMU : D.M ≤ normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
  haveI hN := cTilde_bot_normal D.M D.U hMU
  set e := mbarEquiv D.M D.U with he
  set T : ↥S → Subgroup (F11.MBar11 D.M ⊥ D.U) := fun k => (Nb k).map e.toMonoidHom with hT
  have hTL : ∀ k : ↥S, ∃ n, 2 ≤ n ∧ IsL2Ev ↥(T k) n := by
    intro k
    obtain ⟨n, hn, -⟩ := hcl k
    refine ⟨n, two_le_of_isL2Ev_of_card hn (hS6 k k.2), ?_⟩
    obtain ⟨F, i1, i2, hF, ⟨e₀⟩⟩ := hn
    exact ⟨F, i1, i2, hF, ⟨((Nb k).equivMapOfInjective e.toMonoidHom e.injective).symm.trans e₀⟩⟩
  have hTS : ∀ k, IsSimpleGroup ↥(T k) := fun k => by
    obtain ⟨n, hn2, hn⟩ := hTL k
    exact isSimpleGroup_of_isL2Ev hn hn2
  have hTZ : ∀ k, Subgroup.center ↥(T k) = ⊥ := fun k => by
    obtain ⟨n, -, hn⟩ := hTL k
    exact center_eq_bot_of_isL2Ev hn
  have hT3 : ∀ k, 3 ∣ Nat.card ↥(T k) := fun k => by
    obtain ⟨n, -, hn⟩ := hTL k
    exact three_dvd_card_of_isL2Ev hn
  have hTq : ∀ k, CFSG.Open.IsQuasisimple ↥(T k) := fun k => by
    haveI := hTS k
    exact isQuasisimple_of_isSimpleGroup (hTZ k)
  have hTcomm : ∀ k l, k ≠ l → ∀ x ∈ T k, ∀ y ∈ T l, x * y = y * x := by
    rintro k l hkl _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hNb.1.2.1 k l (fun h => hkl (Subtype.ext h)) x hx y hy]
  have hTcomm' : Pairwise fun k l => ∀ x y, x ∈ T k → y ∈ T l → Commute x y :=
    fun k l hkl x y hx hy => hTcomm k l hkl x hx y hy
  have hTind : iSupIndep T :=
    iSupIndep_map (iSupIndep.comp (P22y.iSupIndep_of hNb.1) Subtype.val_injective) _ e.injective
  set X : Subgroup (F11.MBar11 D.M ⊥ D.U) := ⨆ k, T k with hX
  have hXlayer : rankThreeLayer X = X := rankThreeLayer_iSup_of_comm hTq hTcomm
  set Xp : Subgroup G := F11.barPreimage11 D.M ⊥ D.U X with hXp
  have hXpM : Xp ≤ D.M := Subgroup.map_subtype_le _
  have hCX : F11.CTilde D.M ⊥ D.U ≤ Xp := by
    intro x hx
    have hxM : x ∈ D.M := by
      rw [cTilde_bot] at hx
      exact hx.1
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨x, hxM⟩ ∈ X
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact X.one_mem
  have hbarXp : F11.barImage11 D.M ⊥ D.U Xp = X := by
    unfold F11.barImage11
    rw [hXp]
    unfold F11.barPreimage11
    have h1 : ((X.comap (QuotientGroup.mk' ((F11.CTilde D.M ⊥ D.U).subgroupOf D.M))).map
        D.M.subtype).subgroupOf D.M = X.comap (QuotientGroup.mk' ((F11.CTilde D.M ⊥ D.U).subgroupOf D.M)) :=
      Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
    rw [h1]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) X
  obtain ⟨Y, hY, -⟩ := h119 D.U (uc22p22c_hyp11 D hW c.hU) Xp hCX hXpM
    (by rw [hbarXp]; exact hXlayer)
  obtain ⟨hYX, -, hO2E, -, hYC, hYbar⟩ := hY
  have hYM : Y ≤ D.M := hYX.trans hXpM
  set f : ↥Y →* F11.MBar11 D.M ⊥ D.U :=
    (QuotientGroup.mk' ((F11.CTilde D.M ⊥ D.U).subgroupOf D.M)).comp (Subgroup.inclusion hYM) with hf
  have hfrange : f.range = X := by
    rw [← hbarXp, ← hYbar, hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hfker : ∀ y : ↥Y, y ∈ f.ker ↔ (y : G) ∈ F11.CTilde D.M ⊥ D.U := by
    intro y
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    rfl
  have hlayer : CFSG.layer (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊤ := by
    rw [layer_eq_rankThreeLayer_top]
    set L := rankThreeLayer (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) with hL
    have h1 : (L.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype =
        (⊤ : Subgroup ↥Y).map Y.subtype := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hO2E
    have h2 := Subgroup.map_injective Y.subtype_injective h1
    have h3 := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)) L
    rw [h2, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h3
    exact h3.symm
  have hsolv : Group.IsSolvable ↥f.ker := by
    have hle : f.ker.map Y.subtype ≤ OInf Y := by
      rintro _ ⟨y, hy, rfl⟩
      exact hYC ⟨y.2, (hfker y).1 hy⟩
    haveI := uc22p20a_isSolvable_oinf Y
    exact solvable_of_solvable_injective (f := (Subgroup.inclusion hle).comp
      (f.ker.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
      ((Subgroup.inclusion_injective hle).comp (MulEquiv.injective _))
  have hR : CFSG.pCore 2 ↥Y ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfr : f.range = ⨆ k, T k := hfrange.trans hX
    refine eq_bot_of_isPGroup_two hTcomm' hTind hTS hT3 hTZ (CFSG.pCore_isPGroup.map f) ?_ ?_
    · rw [← hfr]
      exact Subgroup.map_le_range _ _
    · rw [← hfr]
      rintro _ ⟨y, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨y * r * y⁻¹, (CFSG.pCore_normal).conj_mem r hr y, by simp [map_mul, map_inv]⟩
      · rintro ⟨r, hr, hrz⟩
        refine ⟨y⁻¹ * r * y, ?_, ?_⟩
        · have := (CFSG.pCore_normal (p := 2) (G := ↥Y)).conj_mem r hr y⁻¹
          simpa using this
        · rw [map_mul, map_mul, map_inv, hrz]
          group
  set κ : Fin 4 → ↥S := fun j => S.equivFin.symm (Fin.castLE hS4 j) with hκ
  have hκ : Function.Injective κ :=
    S.equivFin.symm.injective.comp (Fin.castLE_injective hS4)
  have hNperf : ∀ j, ⁅T (κ j), T (κ j)⁆ = T (κ j) := by
    intro j
    have h1 := (hTq (κ j)).1
    have h2 : (_root_.commutator ↥(T (κ j))).map (T (κ j)).subtype = ⁅T (κ j), T (κ j)⁆ := by
      rw [_root_.commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [← h2, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hs : ∀ j, ∃ s ∈ T (κ j), orderOf s = 3 := by
    intro j
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 (hT3 (κ j))
    exact ⟨a, a.2, by rw [Subgroup.orderOf_coe, ha]⟩
  choose s hsT hs3 using hs
  have h4 := four_le_pRank_of_layer f hlayer hsolv hR (fun j => T (κ j))
    (fun j => hfrange ▸ le_iSup T (κ j)) hNperf
    (fun j l hjl x hx y hy => hTcomm _ _ (fun h => hjl (hκ h)) x hx y hy)
    (iSupIndep.comp hTind hκ) s hsT hs3
  have h5 := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) Y
  have h6 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hYM
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
