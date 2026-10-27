module

public import CFSG.Sporadic.Recognition.JankoWongCover
public import CFSG.Sporadic.Recognition.LyonsAS4Sylow
public import CFSG.GH74.GLS.Stage12.Interface
public import CFSG.GH74.GLS.Stage12.McLCover

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Sporadic.Recognition.JankoWong

private theorem eq_one_or_eq_of_card_center {K : Type*} [Group K]
    (hc : Nat.card (Subgroup.center K) = 2) {t : K} (ht : t ∈ Subgroup.center K) (ht1 : t ≠ 1)
    {c : K} (hcc : c ∈ Subgroup.center K) : c = 1 ∨ c = t := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center K)).mp hc
  by_cases h1 : c = 1
  · exact Or.inl h1
  · refine Or.inr ?_
    have e1 := huniq ⟨c, hcc⟩ (fun h => h1 (congrArg Subtype.val h))
    have e2 := huniq ⟨t, ht⟩ (fun h => ht1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)

private theorem mem_center_iff_of_centralizer {X : Type*} [Group X] {t : X} (ht1 : t ≠ 1)
    {C : Subgroup X} (hC : C = centralizer ({t} : Set X))
    (hc : Nat.card (Subgroup.center ↥C) = 2) (c : ↥C) :
    c ∈ Subgroup.center ↥C ↔ (c : X) = 1 ∨ (c : X) = t := by
  have htC : t ∈ C := by
    rw [hC]
    exact mem_centralizer_singleton_iff.2 rfl
  have ht'cen : (⟨t, htC⟩ : ↥C) ∈ Subgroup.center ↥C := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : (g : X) ∈ centralizer ({t} : Set X) := by
      rw [← hC]
      exact g.2
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hg)
  constructor
  · intro hcc
    rcases eq_one_or_eq_of_card_center hc ht'cen (fun h => ht1 (congrArg Subtype.val h)) hcc with
      h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · rintro (h | h)
    · have : c = 1 := Subtype.ext h
      rw [this]
      exact Subgroup.one_mem _
    · have : c = ⟨t, htC⟩ := Subtype.ext h
      rw [this]
      exact ht'cen

theorem isCover8_of_isDoubleCoverOfAlt {K : Type} [Group K] (h : IsDoubleCoverOfAlt K 8) :
    ∃ (ρ : K →* Equiv.Perm (Fin 8)) (z : K), IsCover8 ρ z ∧
      Subgroup.center K = Subgroup.zpowers z := by
  obtain ⟨hq, hc, ⟨e⟩⟩ := h
  let ρ : K →* Equiv.Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
  have hker : ∀ x, ρ x = 1 ↔ x ∈ Subgroup.center K := by
    intro x
    simp only [ρ, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom]
    constructor
    · intro hx
      have : e (QuotientGroup.mk' (center K) x) = 1 := Subtype.ext hx
      rw [MulEquiv.map_eq_one_iff] at this
      exact (QuotientGroup.eq_one_iff x).mp this
    · intro hx
      have : QuotientGroup.mk' (center K) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [this, map_one]
      rfl
  obtain ⟨⟨z, hz⟩, hz1, -⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center K)).mp hc
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzpow : z ^ 2 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center K) (x := ⟨z, hz⟩)
    rw [hc] at this
    simpa using congrArg Subtype.val this
  have hcenter_eq : Subgroup.center K = Subgroup.zpowers z := by
    apply le_antisymm
    · intro c hcc
      rcases eq_one_or_eq_of_card_center hc hz hz1' hcc with rfl | rfl
      · exact one_mem _
      · exact mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact hz
  refine ⟨ρ, z, ⟨hz1', hzpow, hz, ?_, ?_, hq.1⟩, hcenter_eq⟩
  · ext x
    rw [MonoidHom.mem_ker, hker, hcenter_eq]
  · ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact (e (QuotientGroup.mk' (center K) x)).2
    · intro hp
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center K) (e.symm ⟨p, hp⟩)
      refine ⟨x, ?_⟩
      have := congrArg e hx
      simp only [MulEquiv.apply_symm_apply] at this
      simpa [ρ] using congrArg Subtype.val this

private theorem normal_le_center_or_eq_top {K : Type*} [Group K] (hq : IsQuasisimple K)
    (M : Subgroup K) [M.Normal] : M ≤ Subgroup.center K ∨ M = ⊤ := by
  obtain ⟨hperf, hs, -⟩ := hq
  have hnorm : (M.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map ‹M.Normal› (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have := hnorm
  rcases hs.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · left
    intro m hm
    have h1 : QuotientGroup.mk' (Subgroup.center K) m ∈
        M.map (QuotientGroup.mk' (Subgroup.center K)) := Subgroup.mem_map_of_mem _ hm
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff m).mp h1
  · right
    have hsup : M ⊔ Subgroup.center K = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center K)) M
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator K ≤ M :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.isPerfect_def.mp hperf] at hle
    exact top_le_iff.mp hle

private theorem conj_eq_inv_of_fixedPointFree {X : Type*} [Group X] (N : Subgroup X) [N.Normal]
    [Finite N] {c : X} (hcc : c * c = 1) (hfix : ∀ n ∈ N, c * n * c⁻¹ = n → n = 1) {n : X}
    (hn : n ∈ N) : c * n * c⁻¹ = n⁻¹ := by
  let φ : N →* N := (MulAut.conjNormal c).toMonoidHom
  have hφ : MonoidHom.FixedPointFree φ := fun a ha =>
    Subtype.ext (hfix a a.2 (by simpa [φ] using congrArg Subtype.val ha))
  have hinv : Function.Involutive φ := fun a => by
    change (MulAut.conjNormal c) ((MulAut.conjNormal c) a) = a
    rw [← MulAut.mul_apply, ← map_mul, hcc, map_one]
    rfl
  have h := congrFun (hφ.coe_eq_inv_of_involutive hinv) ⟨n, hn⟩
  simpa [φ] using congrArg Subtype.val h

private theorem exists_sylow_of_cover8 {X : Type} [Group X] [Finite X] {t : X}
    (ht : orderOf t = 2) {C : Subgroup X} (hC : C = centralizer ({t} : Set X))
    {ρ : ↥C →* Equiv.Perm (Fin 8)} {z : ↥C} (hρ : IsCover8 ρ z) (hzt : (z : X) = t) :
    ∃ T : Subgroup X, T ≤ C ∧ t ∈ T ∧ (∃ S : Sylow 2 X, (S : Subgroup X) = T) ∧
      ∀ c ∈ T, orderOf c = 2 → (∀ s ∈ T, s * c = c * s) → c = t := by
  have hz0 : orderOf z = 2 := orderOf_eq_prime hρ.sq_eq_one hρ.ne_one
  have hzp : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz0]; norm_num)
  obtain ⟨S₀, hzS₀⟩ := hzp.exists_le_sylow
  have hTpg : IsPGroup 2 ((S₀ : Subgroup C).map C.subtype) := S₀.isPGroup'.map C.subtype
  have hzS : z ∈ (S₀ : Subgroup C) := hzS₀ (Subgroup.mem_zpowers z)
  have htT : t ∈ (S₀ : Subgroup C).map C.subtype := ⟨z, hzS, hzt⟩
  have hTle : (S₀ : Subgroup C).map C.subtype ≤ C := Subgroup.map_subtype_le _
  have hodd : Odd (S₀ : Subgroup C).index := by
    have h := S₀.not_dvd_index
    exact Nat.odd_iff.2 (by omega)
  have hTK : Nat.card ((S₀ : Subgroup C).map C.subtype) * (S₀ : Subgroup C).index =
      Nat.card C := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact Subgroup.card_mul_index _
  have hZ : ∀ c ∈ (S₀ : Subgroup C).map C.subtype, orderOf c = 2 →
      (∀ s ∈ (S₀ : Subgroup C).map C.subtype, s * c = c * s) → c = t := by
    rintro c ⟨y, hyS, rfl⟩ hc2 hcs
    have hy : ∀ s ∈ (S₀ : Subgroup C), s * y = y * s := fun s hs =>
      Subtype.ext (hcs _ ⟨s, hs, rfl⟩)
    rcases hρ.eq_one_or_eq_z_of_central S₀ hyS hy with h1 | h1
    · rw [h1] at hc2
      simp at hc2
    · rw [← hzt, h1]
      rfl
  refine ⟨_, hTle, htT, ?_, hZ⟩
  subst hC
  obtain ⟨S, hS⟩ := exists_sylow_central_of_centralizer_sylow ht _ hTle htT hTpg hodd hTK hZ
  exact ⟨S, hS⟩

private theorem normalizer_le_centralizer {X : Type*} [Group X] {t : X} (ht : orderOf t = 2)
    {T : Subgroup X} (hTle : T ≤ centralizer ({t} : Set X)) (htT : t ∈ T)
    (hZ : ∀ c ∈ T, orderOf c = 2 → (∀ s ∈ T, s * c = c * s) → c = t) :
    normalizer (T : Set X) ≤ centralizer ({t} : Set X) := by
  intro n hnN
  have hcT : n * t * n⁻¹ ∈ T := (mem_normalizer_iff.1 hnN t).1 htT
  have hc2 : orderOf (n * t * n⁻¹) = 2 := by
    rw [← ht]
    exact (MulAut.conj n).orderOf_eq t
  have hcentral : ∀ s ∈ T, s * (n * t * n⁻¹) = (n * t * n⁻¹) * s := by
    intro s hs
    have hs' : n⁻¹ * s * n ∈ T := (mem_normalizer_iff''.1 hnN s).1 hs
    have h1 : t * (n⁻¹ * s * n) = (n⁻¹ * s * n) * t :=
      mem_centralizer_singleton_iff.1 (hTle hs') |>.symm
    calc s * (n * t * n⁻¹) = n * ((n⁻¹ * s * n) * t) * n⁻¹ := by group
      _ = n * (t * (n⁻¹ * s * n)) * n⁻¹ := by rw [h1]
      _ = (n * t * n⁻¹) * s := by group
  have hnt : n * t = t * n := mul_inv_eq_iff_eq_mul.1 (hZ _ hcT hc2 hcentral)
  exact mem_centralizer_singleton_iff.2 hnt

private theorem normal_eq_bot_or_top_of_cover8 {X : Type} [Group X] [Finite X] {t : X}
    (ht : orderOf t = 2) {C : Subgroup X} (hC : C = centralizer ({t} : Set X))
    (hcov : IsDoubleCoverOfAlt ↥C 8)
    (hone : ∀ u v : X, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    {T : Subgroup X} (hTC : T ≤ C) (htT : t ∈ T) {S : Sylow 2 X} (hST : (S : Subgroup X) = T)
    (hZ : ∀ c ∈ T, orderOf c = 2 → (∀ s ∈ T, s * c = c * s) → c = t)
    (N : Subgroup X) (hN : N.Normal) : N = ⊥ ∨ N = ⊤ := by
  have ht1 : t ≠ 1 := fun h => by simp [h] at ht
  have hmem : ∀ g : X, g ∈ C ↔ g * t = t * g := fun g => by
    rw [hC]
    exact mem_centralizer_singleton_iff
  have hcen := mem_center_iff_of_centralizer ht1 hC hcov.2.1
  have hnorm : normalizer (T : Set X) ≤ C := by
    rw [hC]
    exact normalizer_le_centralizer ht (by rw [← hC]; exact hTC) htT hZ
  have := hN
  rcases normal_le_center_or_eq_top hcov.1 (N.subgroupOf C) with hle | htop
  · left
    have hNC : ∀ n ∈ N, n ∈ C → n = 1 ∨ n = t := fun n hnN hnC =>
      (hcen ⟨n, hnC⟩).1 (hle (mem_subgroupOf.2 hnN))
    obtain ⟨c, hc2, hcn⟩ := McLRec.exists_noncentral_involution_of_doubleCover hcov
    have hcX1 : (c : X) ≠ 1 := fun h => hcn ((hcen c).2 (Or.inl h))
    have hcX : (c : X) ^ 2 = 1 := by simpa using congrArg Subtype.val hc2
    have hcX2 : orderOf (c : X) = 2 := orderOf_eq_prime hcX hcX1
    have htN : t ∉ N := by
      intro htN
      obtain ⟨g, hg⟩ := isConj_iff.1 (hone (c : X) t hcX2 ht)
      have hcN : (c : X) ∈ N := by
        have h1 := hN.conj_mem t htN g⁻¹
        rw [← hg] at h1
        have h2 : g⁻¹ * (g * (c : X) * g⁻¹) * g⁻¹⁻¹ = c := by group
        rwa [h2] at h1
      exact hcn ((hcen c).2 (hNC c hcN c.2))
    have hN1 : ∀ n ∈ N, t * n = n * t → n = 1 := by
      intro n hnN hnt
      rcases hNC n hnN ((hmem n).2 hnt.symm) with h | h
      · exact h
      · exact absurd (h ▸ hnN) htN
    have hfix : ∀ d : X, orderOf d = 2 → ∀ n ∈ N, d * n * d⁻¹ = n → n = 1 := by
      intro d hd n hn hdn
      obtain ⟨g, hg⟩ := isConj_iff.1 (hone t d ht hd)
      have hm : t * (g⁻¹ * n * g) = (g⁻¹ * n * g) * t := by
        have h1 : (g * t * g⁻¹) * n * (g * t * g⁻¹)⁻¹ = n := by
          rw [hg]
          exact hdn
        calc t * (g⁻¹ * n * g)
            = g⁻¹ * ((g * t * g⁻¹) * n * (g * t * g⁻¹)⁻¹ * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * (n * (g * t * g⁻¹)) * g := by rw [h1]
          _ = (g⁻¹ * n * g) * t := by group
      have hm1 : g⁻¹ * n * g = 1 :=
        hN1 _ (by simpa using hN.conj_mem n hn g⁻¹) hm
      calc n = g * (g⁻¹ * n * g) * g⁻¹ := by group
        _ = 1 := by rw [hm1]; group
    have hinv : ∀ d : X, orderOf d = 2 → ∀ n ∈ N, d * n * d⁻¹ = n⁻¹ := by
      intro d hd n hn
      have hdd : d * d = 1 := by
        have := pow_orderOf_eq_one d
        rwa [hd, pow_two] at this
      exact conj_eq_inv_of_fixedPointFree N hdd (hfix d hd) hn
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht, pow_two] at this
    have hcc : (c : X) * c = 1 := by
      have := pow_orderOf_eq_one (c : X)
      rwa [hcX2, pow_two] at this
    have htc : t * (c : X) = c * t := ((hmem c).1 c.2).symm
    have htcc : (t * (c : X)) * (t * (c : X)) = 1 := by
      calc (t * (c : X)) * (t * (c : X)) = t * ((c : X) * t) * c := by group
        _ = t * (t * (c : X)) * c := by rw [htc]
        _ = (t * t) * ((c : X) * c) := by group
        _ = 1 := by rw [htt, hcc, one_mul]
    have htc1 : t * (c : X) ≠ 1 := by
      intro h
      have h2 : (c : X) = t⁻¹ := eq_inv_of_mul_eq_one_right h
      exact hcn ((hcen c).2 (Or.inr (by rw [h2, inv_eq_of_mul_eq_one_right htt])))
    have hord : orderOf (t * (c : X)) = 2 := orderOf_eq_prime (by rw [pow_two]; exact htcc) htc1
    refine eq_bot_iff.2 fun n hn => ?_
    rw [Subgroup.mem_bot]
    refine hfix (t * c) hord n hn ?_
    calc t * (c : X) * n * (t * (c : X))⁻¹ = t * ((c : X) * n * (c : X)⁻¹) * t⁻¹ := by group
      _ = t * n⁻¹ * t⁻¹ := by rw [hinv c hcX2 n hn]
      _ = (t * n * t⁻¹)⁻¹ := by group
      _ = n := by rw [hinv t ht n hn, inv_inv]
  · right
    have hCN : C ≤ N := fun c hc => by
      have : (⟨c, hc⟩ : ↥C) ∈ N.subgroupOf C := by
        rw [htop]
        trivial
      exact mem_subgroupOf.1 this
    have hSN : (S : Subgroup X) ≤ N := hST ▸ hTC.trans hCN
    have hfrat : normalizer (S : Set X) ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top' S hSN
    rw [eq_top_iff, ← hfrat]
    refine sup_le (fun n hn => hCN (hnorm ?_)) le_rfl
    rw [← hST]
    exact hn

theorem simple_of_oneClass_cover8 {X : Type} [Group X] [Finite X] {t : X} (ht : orderOf t = 2)
    (hcov : IsDoubleCoverOfAlt ↥(centralizer ({t} : Set X)) 8)
    (hone : ∀ u v : X, orderOf u = 2 → orderOf v = 2 → IsConj u v) :
    IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧ OneClassDoubleCover X 8 := by
  have hcov0 := hcov
  generalize hC : centralizer ({t} : Set X) = C at hcov
  have hC' : C = centralizer ({t} : Set X) := hC.symm
  have ht1 : t ≠ 1 := fun h => by simp [h] at ht
  have hmem : ∀ g : X, g ∈ C ↔ g * t = t * g := fun g => by
    rw [hC']
    exact mem_centralizer_singleton_iff
  obtain ⟨ρ, z, hρ, -⟩ := isCover8_of_isDoubleCoverOfAlt hcov
  have hcen := mem_center_iff_of_centralizer ht1 hC' hcov.2.1
  have hzt : (z : X) = t :=
    ((hcen z).1 hρ.central).resolve_left fun h => hρ.ne_one (Subtype.ext h)
  obtain ⟨T, hTC, htT, ⟨S, hST⟩, hZ⟩ := exists_sylow_of_cover8 ht hC' hρ hzt
  have hnonab : ∃ a b : X, a * b ≠ b * a := by
    obtain ⟨-, -, a, b, hab⟩ := hcov.1
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a', b', fun h => hab ?_⟩
    have : a' * b' = b' * a' := Subtype.ext h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
  refine ⟨?_, hnonab, ?_⟩
  · exact
      { toNontrivial := ⟨⟨t, 1, ht1⟩⟩
        eq_bot_or_eq_top_of_normal := fun N hN =>
          normal_eq_bot_or_top_of_cover8 ht hC' hcov hone hTC htT hST hZ N hN }
  · refine ⟨t, ⟨ht, S, hST ▸ htT, fun s hs => ?_⟩, hone, hcov0⟩
    have hsC : s ∈ C := hTC (hST ▸ hs)
    exact (hmem s).1 hsC

end CFSG.Sporadic.Recognition.LyonsSims
