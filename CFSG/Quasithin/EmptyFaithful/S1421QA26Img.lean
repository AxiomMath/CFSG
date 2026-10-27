module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Model
import CFSG.Quasithin.EmptyFaithful.R3cBase
import CFSG.Quasithin.H13.NQRigidWMGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.QA26

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Bridge

@[expose] def NoA7Image (Γ : Type) [Group Γ] : Prop :=
  ∀ (H : Type) [Group H] (π : Γ →* H), Function.Surjective π →
    ¬ Nonempty (H ≃* alternatingGroup (Fin 7))

theorem card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]; decide

theorem card_two_or_four_le {K : Type} [Field K] [Finite K] {n : ℕ} (hn : Nat.card K = 2 ^ n) :
    Nat.card K = 2 ∨ (2 ≤ n ∧ 4 ≤ Nat.card K) := by
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  rcases Nat.lt_or_ge n 2 with h | h
  · left
    interval_cases n
    · rw [hn] at h1
      omega
    · rw [hn]
      norm_num
  · right
    refine ⟨h, ?_⟩
    rw [hn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h

theorem noA7Image_of_mulEquiv {Γ Γ' : Type} [Group Γ] [Group Γ'] (e : Γ' ≃* Γ)
    (h : NoA7Image Γ) : NoA7Image Γ' := by
  intro H _ π hπ
  exact h H (π.comp e.symm.toMonoidHom) (hπ.comp e.symm.surjective)

theorem noA7Image_of_not_dvd {Γ : Type} [Group Γ] [Finite Γ] (h : ¬ 2520 ∣ Nat.card Γ) :
    NoA7Image Γ := by
  intro H _ π hπ ⟨e⟩
  apply h
  have h1 : Nat.card H ∣ Nat.card Γ := Subgroup.card_dvd_of_surjective hπ
  rwa [Nat.card_congr e.toEquiv, card_alt_seven] at h1

theorem noA7Image_of_simple {Γ : Type} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    (h : Nat.card Γ ≠ 2520) : NoA7Image Γ := by
  intro H _ π hπ ⟨e⟩
  have : Nontrivial (alternatingGroup (Fin 7)) := (alt_isSimple (by norm_num)).toNontrivial
  have : Nontrivial H := e.toEquiv.nontrivial
  have hinj : Function.Injective π := injective_of_surjective_of_simple π hπ
  apply h
  rw [Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩), Nat.card_congr e.toEquiv, card_alt_seven]

theorem noA7Image_of_noAlt57Image {Γ : Type} [Group Γ] (h : NoAlt57Image Γ) : NoA7Image Γ := by
  intro H _ π hπ ⟨e⟩
  exact h H π hπ ⊤ inferInstance (fun _ => Subgroup.mem_top _) 7 (Or.inr rfl)
    ⟨Subgroup.topEquiv.trans e⟩

theorem noA7Image_alt {m : ℕ} (hm : m = 5 ∨ m = 6 ∨ m = 8) :
    NoA7Image ↥(alternatingGroup (Fin m)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin m)) := alt_isSimple (by omega)
  refine noA7Image_of_simple ?_
  rcases hm with rfl | rfl | rfl
  · rw [card_alt_five]; norm_num
  · rw [card_alt_six]; norm_num
  · rw [card_alt_eight]; norm_num

theorem noA7Image_sl3_of_card_two (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    NoA7Image ↥(StatedSL 3 K) := by
  have : Finite ↥(StatedSL 3 K) :=
    Finite.of_equiv _ (specialLinearGroupEquivStatedSL 3 K).toEquiv
  refine noA7Image_of_not_dvd ?_
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
    Alt57.card_sl3_field K, hK]
  norm_num

theorem noA7Image_slTwo {d : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 5) :
    NoA7Image ↥(StatedSL d (ZMod 2)) := by
  rcases hd with rfl | rfl | rfl
  · exact noA7Image_sl3_of_card_two (ZMod 2) (by rw [Nat.card_eq_fintype_card, ZMod.card])
  · exact noA7Image_of_noAlt57Image noAlt57Image_sl4
  · exact noA7Image_of_noAlt57Image noAlt57Image_sl5

theorem noA7Image_sp4 (K : Type) [Field K] [Finite K] (hK : ∃ n : ℕ, Nat.card K = 2 ^ n) :
    NoA7Image ↥(StatedSp 2 K) :=
  noA7Image_of_noAlt57Image (alt57ModelFacts.sp4 K hK)

theorem noA7Image_g2 (K : Type) [Field K] [Finite K] (hK : ∃ n : ℕ, Nat.card K = 2 ^ n) :
    NoA7Image ↥(CFSG.Open.quasithinG2 K) :=
  noA7Image_of_noAlt57Image (alt57ModelFacts.g2 K hK)

theorem noA7Image_g2derived (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    NoA7Image ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ := by
  have hchar : CharP K 2 :=
    CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow (f := 1) (by rw [hK]; norm_num)
  intro H _ π hπ ⟨e⟩
  have hle : ⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ ≤ CFSG.Open.quasithinG2 K := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    rw [commutatorElement_def]
    exact (CFSG.Open.quasithinG2 K).mul_mem ((CFSG.Open.quasithinG2 K).mul_mem
      ((CFSG.Open.quasithinG2 K).mul_mem hg hk) ((CFSG.Open.quasithinG2 K).inv_mem hg))
      ((CFSG.Open.quasithinG2 K).inv_mem hk)
  have h1 : Nat.card H ∣ Nat.card ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
    Subgroup.card_dvd_of_surjective hπ
  have h2 := Subgroup.card_dvd_of_le hle
  have h3 : Nat.card ↥(CFSG.Open.quasithinG2 K) =
      Nat.card ↥(CFSG.Quasithin.Explicit.cayleyGroup K) := by
    rw [Alt57Model.quasithinG2_eq_cayleyGroup]
  have h5 : 5 ∣ Nat.card H := by
    rw [Nat.card_congr e.toEquiv, card_alt_seven]; norm_num
  exact Alt57Model.not_five_dvd_card_cayley hK (h3 ▸ h5.trans (h1.trans h2))

theorem noA7Image_sl2 (K : Type) [Field K] [Finite K] (hK : ∃ n : ℕ, Nat.card K = 2 ^ n) :
    NoA7Image ↥(StatedSL 2 K) := by
  obtain ⟨n, hn⟩ := hK
  have : Finite ↥(StatedSL 2 K) :=
    Finite.of_equiv _ (specialLinearGroupEquivStatedSL 2 K).toEquiv
  have hcard : Nat.card ↥(StatedSL 2 K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 2 K).toEquiv]
    exact CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K
  rcases card_two_or_four_le hn with h2 | ⟨-, h4⟩
  · refine noA7Image_of_not_dvd ?_
    rw [hcard, h2]
    norm_num
  · have hchar : CharP K 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hn
    have : IsSimpleGroup ↥(StatedSL 2 K) :=
      CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
    refine noA7Image_of_simple ?_
    intro h2520
    rw [hcard, hn] at h2520
    have := (Alt57.sl2_card ⟨n, rfl⟩ (Or.inr h2520)).2
    omega

theorem noA7Image_sl3 (K : Type) [Field K] [Finite K] (hK : ∃ n : ℕ, Nat.card K = 2 ^ n) :
    NoA7Image ↥(StatedSL 3 K) := by
  obtain ⟨n, hn⟩ := hK
  rcases card_two_or_four_le hn with h2 | ⟨hn2, h4⟩
  · exact noA7Image_sl3_of_card_two K h2
  · intro H _ π hπ ⟨e⟩
    have hchar : CharP K 2 := CFSG.Quasithin.R3c.charP_two_of_natCard_eq_two_pow hn
    obtain ⟨c, hc0, hc1⟩ := Alt57Model.exists_ne_zero_one h4
    have hφ := Alt57Model.sl3_image_trivial hn hn2 (m := 7) (Or.inr rfl) hc0 hc1
      (e.toMonoidHom.comp (π.comp (specialLinearGroupEquivStatedSL 3 K).toMonoidHom))
    have : Nontrivial (alternatingGroup (Fin 7)) := (alt_isSimple (by norm_num)).toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : alternatingGroup (Fin 7))
    obtain ⟨g, hg⟩ := hπ (e.symm x)
    obtain ⟨A, rfl⟩ := (specialLinearGroupEquivStatedSL 3 K).surjective g
    apply hx
    have h5 := hφ A
    simpa [hg] using h5

theorem noA7Image_hat {Γ : Type} [Group Γ] (h : IsHat Γ (alternatingGroup (Fin 6))) :
    NoA7Image Γ := by
  obtain ⟨-, hZ, ⟨e⟩⟩ := h
  have hQ : Nat.card (Γ ⧸ Subgroup.center Γ) = 360 := by
    rw [Nat.card_congr e.toEquiv, card_alt_six]
  have : Finite ↥(Subgroup.center Γ) := Nat.finite_of_card_ne_zero (by omega)
  have : Finite (Γ ⧸ Subgroup.center Γ) := Nat.finite_of_card_ne_zero (by omega)
  have : Finite Γ :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := Subgroup.center Γ)).symm
  refine noA7Image_of_not_dvd ?_
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Γ), hQ, hZ]
  norm_num

end CFSG.Quasithin.QA26
