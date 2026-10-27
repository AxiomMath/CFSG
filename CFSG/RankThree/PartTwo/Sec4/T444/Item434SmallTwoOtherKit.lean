module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
public import CFSG.RankThree.PartTwo.KFacts.KS21SylowCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores
open Item434Kit Item434Alt
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Hyper

variable {X : Type*} [Group X]

@[expose] def hyperCent (P : Subgroup X) : Set X :=
  {x | ∃ R : Subgroup X, R ≤ P ∧ 3 * Nat.card R = Nat.card P ∧ ∀ r ∈ R, r * x = x * r}

theorem mem_hyperCent_of_commute {P : Subgroup X} (hP9 : Nat.card P = 9) {p x : X} (hp : p ∈ P)
    (hp3 : p ^ 3 = 1) (hp1 : p ≠ 1) (hpx : p * x = x * p) : x ∈ hyperCent P := by
  refine ⟨Subgroup.zpowers p, Subgroup.zpowers_le.mpr hp, ?_, fun r hr => ?_⟩
  · rw [Nat.card_zpowers, orderOf_eq_prime hp3 hp1, hP9]
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    exact (Commute.zpow_left hpx k).eq

theorem conj_mem_hyperCent {P : Subgroup X} (g : X) {x : X} (hx : x ∈ hyperCent P) :
    MulAut.conj g x ∈ hyperCent (P.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨R, hRP, hR3, hRx⟩ := hx
  refine ⟨R.map (MulAut.conj g).toMonoidHom, Subgroup.map_mono hRP, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective, hR3]
  · rintro _ ⟨r, hr, rfl⟩
    change MulAut.conj g r * MulAut.conj g x = MulAut.conj g x * MulAut.conj g r
    rw [← map_mul, ← map_mul, hRx r hr]

theorem closure_hyperCent_map_conj {P : Subgroup X} (hP : Subgroup.closure (hyperCent P) = ⊤)
    (g : X) : Subgroup.closure (hyperCent (P.map (MulAut.conj g).toMonoidHom)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : (MulAut.conj g).symm y ∈ Subgroup.closure (hyperCent P) := by
    rw [hP]
    exact Subgroup.mem_top _
  have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hy
  rw [MonoidHom.map_closure] at h1
  have h2 : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) = y :=
    (MulAut.conj g).apply_symm_apply y
  rw [h2] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨x, hx, rfl⟩
  exact conj_mem_hyperCent g hx

theorem exists_map_conj_of_sylow [Finite X] {P₀ P : Subgroup X}
    (hP₀ : Nat.card P₀ = 3 ^ (Nat.card X).factorization 3) (hP : Nat.card P = Nat.card P₀) :
    ∃ g : X, P = P₀.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (by rw [hP, hP₀])
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hP₀ hPp
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP]

end Hyper

theorem exists_map_conj_of_maxEA {X : Type} [Group X] [Finite X] (hX : KFacts.KS21.MaxEA X 3)
    {E₀ P : Subgroup X}
    (hE₀ : CFSG.Assembly.IsElemAbelian 3 E₀) (hE₀27 : Nat.card E₀ = 27)
    (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP27 : Nat.card P = 27) :
    ∃ g : X, P = E₀.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE₀p : IsPGroup 3 E₀ := IsPGroup.of_card (n := 3) (by rw [hE₀27]; norm_num)
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 3) (by rw [hP27]; norm_num)
  obtain ⟨S₀, hS₀⟩ := hE₀p.exists_le_sylow
  obtain ⟨S, hS⟩ := hPp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₀ S
  have hle := KFacts.KS21.map_conj_inv_le hg hS
  have heq := hX.2 S₀ _ _ hle hS₀
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ P hP) hE₀
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP27]; norm_num)
    (by rw [hE₀27]; norm_num)
  refine ⟨g, ?_⟩
  rw [← heq, Subgroup.map_map]
  ext y
  simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, MulAut.conj_apply]
  constructor
  · intro hy
    exact ⟨y, hy, by group⟩
  · rintro ⟨x, hx, rfl⟩
    convert hx using 1
    group


section Ctx

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem card_map_quotConj_dvd [Finite X] (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hout : ¬ 3 ∣ Nat.card (Outer X)) :
    Nat.card (A.map (quotConj e)) ∣ Nat.card X := by
  have hle : A.map (quotConj e) ≤ (MulAut.conj : X →* MulAut X).range := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_range_conj_of_pow_three hout (by rw [← map_pow, h.isE27.1.2 a ha, map_one])
  have h1 : Nat.card (A.map (quotConj e)) ∣ Nat.card (MulAut.conj : X →* MulAut X).range :=
    Subgroup.card_dvd_of_le hle
  exact h1.trans (Subgroup.card_range_dvd _)

theorem false_of_not_nine_dvd [Finite X] (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hout : ¬ 3 ∣ Nat.card (Outer X))
    (h9 : ¬ 9 ∣ Nat.card X) : False := by
  have hd := card_map_quotConj_dvd h e hout
  rw [Item434Spor.card_map_quotConj h e] at hd
  rcases h.card_layerStar with h9' | ⟨h27, -⟩
  · rw [h9'] at hd
    exact h9 hd
  · rw [h27] at hd
    exact h9 ((by norm_num : (9 : ℕ) ∣ 27).trans hd)

theorem exists_inner_of_inner (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hinner : ∀ φ : MulAut X, φ ^ 3 = 1 → φ ∈ (MulAut.conj : X →* MulAut X).range)
    (hcen : Subgroup.center X = ⊥) :
    ∃ P : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P ∧ Nat.card P = Nat.card h.layerStar ∧
      A.map (quotConj e) = P.map MulAut.conj := by
  set P := (A.map (quotConj e)).comap (MulAut.conj : X →* MulAut X) with hP
  have hPmap : P.map MulAut.conj = A.map (quotConj e) := by
    apply Subgroup.map_comap_eq_self
    rintro _ ⟨a, ha, rfl⟩
    exact hinner _ (by rw [← map_pow, h.isE27.1.2 a ha, map_one])
  have hinj := conj_injective_of_center_eq_bot hcen
  refine ⟨P, isElemAbelian_of_map_injective hinj ?_, ?_, hPmap.symm⟩
  · rw [hPmap]
    exact isElemAbelian_map_quotConj h e
  · rw [← Subgroup.card_map_of_injective hinj, hPmap, Item434Spor.card_map_quotConj h e]

theorem exists_inner (h : Ctx434Core G A M Q) (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hout : ¬ 3 ∣ Nat.card (Outer X)) (hcen : Subgroup.center X = ⊥) :
    ∃ P : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P ∧ Nat.card P = Nat.card h.layerStar ∧
      A.map (quotConj e) = P.map MulAut.conj :=
  exists_inner_of_inner h e (fun _ hφ => mem_range_conj_of_pow_three hout hφ) hcen

theorem card_inf_comap_eq_nine (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hcen : Subgroup.center X = ⊥)
    {P : Subgroup X} (hP : A.map (quotConj e) = P.map MulAut.conj) {R : Subgroup X}
    (hRP : R ≤ P) (hR3 : 3 * Nat.card R = Nat.card P) :
    Nat.card (A ⊓ (R.map (MulAut.conj : X →* MulAut X)).comap (quotConj e) : Subgroup G) = 9 := by
  have hinj := conj_injective_of_center_eq_bot hcen
  set F := R.map (MulAut.conj : X →* MulAut X) with hF
  set B := A ⊓ F.comap (quotConj e) with hB
  have hFA : F ≤ A.map (quotConj e) := hP ▸ Subgroup.map_mono hRP
  have hBmap : B.map (quotConj e) = F := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact hb.2
    · intro φ hφ
      obtain ⟨a, ha, rfl⟩ := hFA hφ
      exact ⟨a, ⟨ha, hφ⟩, rfl⟩
  have hBker : B ⊓ (quotConj e).ker = A ⊓ (quotConj e).ker := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_left
    · rintro c ⟨hcA, hcK⟩
      refine ⟨⟨hcA, ?_⟩, hcK⟩
      change quotConj e c ∈ F
      rw [MonoidHom.mem_ker.mp hcK]
      exact F.one_mem
  have hB := card_eq_card_inf_ker_mul_card_map (quotConj e) B
  rw [hBker, hBmap, hF, Subgroup.card_map_of_injective hinj] at hB
  have hA := card_eq_card_inf_ker_mul_card_map (quotConj e) A
  rw [hP, Subgroup.card_map_of_injective hinj, h.isE27.2, ← hR3] at hA
  rw [hB]
  have : 3 * (Nat.card (A ⊓ (quotConj e).ker : Subgroup G) * Nat.card R) = 27 := by
    rw [hA]
    ring
  omega

theorem false_of_closure_hyperCent (h : Ctx434Core G A M Q)
    (hZ : Subgroup.center (layer G) = ⊥) (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hcen : Subgroup.center X = ⊥) {P : Subgroup X} (hP : A.map (quotConj e) = P.map MulAut.conj)
    (hgen : Subgroup.closure (hyperCent P) = ⊤) : False := by
  apply h.not_le
  set ι := layerEquiv e hZ with hι
  set R' : Subgroup (layer G) := M.comap (layer G).subtype with hR'
  have hsub : hyperCent P ⊆ (R'.map ι.toMonoidHom : Set X) := by
    rintro x ⟨R, hRP, hR3, hRx⟩
    set F := R.map (MulAut.conj : X →* MulAut X) with hF
    set B := A ⊓ F.comap (quotConj e) with hB
    have hB9 : 9 ≤ Nat.card B := (card_inf_comap_eq_nine h e hcen hP hRP hR3).ge
    refine ⟨ι.symm x, ?_, ι.apply_symm_apply x⟩
    change ((ι.symm x : layer G) : G) ∈ M
    have hyB : ((ι.symm x : layer G) : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨r, hr, hrb⟩ := hb.2
      have hfix : quotConj e b x = x := by
        rw [← hrb, MulAut.conj_apply, hRx r hr, mul_inv_cancel_right]
      have hconj : layerConj G b (ι.symm x) = ι.symm x := by
        apply layerQuot_injective e hZ
        rw [← quotConj_layerQuot]
        have hx' : layerQuot e (ι.symm x) = x := ι.apply_symm_apply x
        rw [hx', hfix]
      have h1 : b * ((ι.symm x : layer G) : G) * b⁻¹ = ι.symm x := by
        rw [← layerConj_apply_coe, hconj]
      calc b * ((ι.symm x : layer G) : G) = b * ((ι.symm x : layer G) : G) * b⁻¹ * b := by group
        _ = ((ι.symm x : layer G) : G) * b := by rw [h1]
    exact (Subgroup.centralizer_le_normalizer _).trans (normalizer_le h inf_le_left hB9) hyB
  have htop : (⊤ : Subgroup X) ≤ R'.map ι.toMonoidHom := by
    rw [← hgen, Subgroup.closure_le]
    exact hsub
  intro y hy
  obtain ⟨z, hz, hzy⟩ := htop (Subgroup.mem_top (ι ⟨y, hy⟩))
  have hzeq : z = ⟨y, hy⟩ := ι.injective hzy
  rw [hzeq] at hz
  exact hz

theorem false_of_gen_of_inner (h : Ctx434Core G A M Q) (hZ : Subgroup.center (layer G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X)
    (hinner : ∀ φ : MulAut X, φ ^ 3 = 1 → φ ∈ (MulAut.conj : X →* MulAut X).range)
    (hcen : Subgroup.center X = ⊥)
    (hgen : ∀ P : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P →
      Nat.card P = Nat.card h.layerStar → Subgroup.closure (hyperCent P) = ⊤) : False := by
  obtain ⟨P, hPe, hPc, hP⟩ := exists_inner_of_inner h e hinner hcen
  exact false_of_closure_hyperCent h hZ e hcen hP (hgen P hPe hPc)

theorem false_of_gen (h : Ctx434Core G A M Q) (hZ : Subgroup.center (layer G) = ⊥)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hout : ¬ 3 ∣ Nat.card (Outer X))
    (hcen : Subgroup.center X = ⊥)
    (hgen : ∀ P : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P →
      Nat.card P = Nat.card h.layerStar → Subgroup.closure (hyperCent P) = ⊤) : False :=
  false_of_gen_of_inner h hZ e (fun _ hφ => mem_range_conj_of_pow_three hout hφ) hcen hgen

end Ctx

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther
