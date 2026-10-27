module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H58
public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def toModO2 (M₁ J K : Subgroup G) (hKJ : K ≤ J) (hJM : J ≤ M₁) :
    ↥K →* ↥(modO2Image M₁ J) :=
  ((QuotientGroup.mk' (CFSG.pCore 2 ↥M₁)).comp (Subgroup.inclusion (hKJ.trans hJM))).codRestrict
    _ fun k => ⟨⟨k, hKJ.trans hJM k.2⟩, hKJ k.2, rfl⟩

theorem toModO2_coe {M₁ J K : Subgroup G} (hKJ : K ≤ J) (hJM : J ≤ M₁) (k : ↥K) :
    ((toModO2 M₁ J K hKJ hJM k : ↥(modO2Image M₁ J)) : ↥M₁ ⧸ CFSG.pCore 2 ↥M₁) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨k, hKJ.trans hJM k.2⟩ := rfl

theorem mem_range_toModO2_iff {M₁ J K : Subgroup G} (hKJ : K ≤ J) (hJM : J ≤ M₁)
    (y : ↥(modO2Image M₁ J)) :
    y ∈ (toModO2 M₁ J K hKJ hJM).range ↔ (y : ↥M₁ ⧸ CFSG.pCore 2 ↥M₁) ∈ modO2Image M₁ K := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k, hKJ.trans hJM k.2⟩, k.2, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    rw [toModO2_coe, ← hxy]

theorem range_toModO2 {M₁ J K : Subgroup G} (hKJ : K ≤ J) (hJM : J ≤ M₁) :
    (toModO2 M₁ J K hKJ hJM).range = (modO2Image M₁ K).subgroupOf (modO2Image M₁ J) := by
  ext y
  rw [mem_range_toModO2_iff, Subgroup.mem_subgroupOf]

variable [Finite G]

omit [Finite G] in
theorem isPGroup_ker_toModO2 {M₁ J K : Subgroup G} (hKJ : K ≤ J) (hJM : J ≤ M₁) :
    IsPGroup 2 ↥(toModO2 M₁ J K hKJ hJM).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro k
  have hk : QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨(k : ↥K), hKJ.trans hJM (k : ↥K).2⟩ = 1 := by
    rw [← toModO2_coe hKJ hJM, MonoidHom.mem_ker.mp k.2]
    rfl
  have hQ := (QuotientGroup.eq_one_iff _).mp hk
  obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥M₁) ⟨_, hQ⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun x => ((x : ↥M₁) : G)) (congrArg Subtype.val hn)
  simpa using this

omit [Finite G] in
theorem two_dvd_index_ker {M₁ J K : Subgroup G} (hKJ : K ≤ J) (hJM : J ≤ M₁)
    (hKp : ⁅K, K⁆ = K) {F : Type} [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    2 ∣ (toModO2 M₁ J K hKJ hJM).ker.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hKp]
  have hle : (toModO2 M₁ J K hKJ hJM).ker ≤ CFSG.pCore 2 ↥K :=
    le_sSup ⟨(toModO2 M₁ J K hKJ hJM).normal_ker, isPGroup_ker_toModO2 hKJ hJM⟩
  have h2 := SL2Inv.two_dvd_card_quot hKtop hF e
  rw [← Subgroup.index_eq_card] at h2
  exact h2.trans (Subgroup.index_dvd_of_le hle)

theorem inf_oddCore_eq_bot_of_SL2 {M₁ J K : Subgroup G} (hKJ : K ≤ J) (hJM : J ≤ M₁)
    (hKp : ⁅K, K⁆ = K) {F : Type} [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    (modO2Image M₁ K).subgroupOf (modO2Image M₁ J) ⊓ CFSG.oddCore ↥(modO2Image M₁ J) = ⊥ := by
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hKp]
  rw [← range_toModO2 hKJ hJM]
  exact SL2Inv.range_inf_eq_bot _ (isPGroup_ker_toModO2 hKJ hJM)
    (SL2Inv.isSimpleGroup_quot hKtop hF e) (SL2Inv.two_dvd_card_quot hKtop hF e)
    (QuasithinUnique.EscapingLocal.odd_card_oddCore _)

omit [Finite G] in
theorem mk_mem_normalizer {M₁ J : Subgroup G} {b : G} (hbM : b ∈ M₁)
    (hbJ : b ∈ Subgroup.normalizer (J : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨b, hbM⟩ ∈
      Subgroup.normalizer (modO2Image M₁ J : Set (↥M₁ ⧸ CFSG.pCore 2 ↥M₁)) := by
  have key : ∀ c : G, ∀ hc : c ∈ M₁, c ∈ Subgroup.normalizer (J : Set G) →
      ∀ y ∈ modO2Image M₁ J, QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨c, hc⟩ * y *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨c, hc⟩)⁻¹ ∈ modO2Image M₁ J := by
    intro c hc hcJ y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨⟨c, hc⟩ * x * ⟨c, hc⟩⁻¹, ?_, by simp⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp hcJ _).mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key b hbM hbJ y, fun hy => ?_⟩
  have h := key b⁻¹ (M₁.inv_mem hbM) (Subgroup.inv_mem _ hbJ) _ hy
  have e : QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨b⁻¹, M₁.inv_mem hbM⟩ =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥M₁) ⟨b, hbM⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e, inv_inv] at h
  simpa [mul_assoc] using h

omit [Finite G] in
theorem commutator_eq_bot_of_isQuasisimple {Y : Type} [Group Y] (hq : CFSG.IsQuasisimple Y)
    {N : Subgroup Y} [hN : N.Normal] {a b : Y} (hab : (a : Y ⧸ N) * b ≠ b * a) :
    ⁅N, (⊤ : Subgroup Y)⁆ = ⊥ := by
  obtain ⟨-, hs, -⟩ := hq
  have hNm : (N.map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hNm with hbot | htop
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.coe_top, Subgroup.centralizer_univ]
    intro x hx
    have h : QuotientGroup.mk' (Subgroup.center Y) x ∈ N.map (QuotientGroup.mk' _) := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h
    exact (QuotientGroup.eq_one_iff x).mp h
  · exfalso
    apply hab
    have hdec : ∀ y : Y, ∃ n ∈ N, ∃ z ∈ Subgroup.center Y, y = n * z := by
      intro y
      have hy : QuotientGroup.mk' (Subgroup.center Y) y ∈ N.map (QuotientGroup.mk' _) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hny⟩ := hy
      refine ⟨n, hn, n⁻¹ * y, ?_, by group⟩
      exact (QuotientGroup.eq (s := Subgroup.center Y)).mp hny
    obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdec a
    obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdec b
    have e1 : ((n₁ * z₁ : Y) : Y ⧸ N) = z₁ := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n₁).mpr hn₁, one_mul]
    have e2 : ((n₂ * z₂ : Y) : Y ⧸ N) = z₂ := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n₂).mpr hn₂, one_mul]
    rw [e1, e2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.mp hz₁ z₂]

omit [Finite G] in
theorem mem_normalizer_of_map_le {K : Subgroup G} {b : G}
    (h1 : K.map (MulAut.conj b).toMonoidHom ≤ K)
    (h2 : K.map (MulAut.conj b⁻¹).toMonoidHom ≤ K) : b ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact h1 ⟨h, hh, rfl⟩
  · intro hh
    have := h2 ⟨_, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch10.SecB
