
module

public import Certificates.Kernel.A7Rad.Checks
public import CFSG.Certificates.Kernel.A7Rad.Sound
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.A7RadicalBase
public import CFSG.Assembly.QuasithinDefs

public section

namespace CertificateChecks.KernelA7Rad

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.A7Rad CFSG.KD.A7Rad
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour CFSG.Open CFSG.Quasithin

theorem isPGroup_of_iff {L n : ℕ} {P : Subgroup A7} (hP : ∀ x, x ∈ P ↔ memP L n (cd x) = true)
    (h4 : pow4B L n = true) : IsPGroup 2 ↥P := fun g => ⟨2, Subtype.ext (by
  have : g.1 ^ 4 = 1 := pow4_sound h4 ((hP g.1).1 g.2)
  simpa using this)⟩

theorem not_rad {P n T m z : ℕ} {Q : Subgroup A7} (hQ : ∀ x, x ∈ Q ↔ memP P n (cd x) = true)
    (hT : closedB T m = true) (hvP : validB P n = true) (hvT : validB T m = true)
    (h4 : pow4B T m = true) (hc : conjB T m P n = true) (hn : normB P n T m z = true)
    (he : exB T m P n = true) : ¬ IsTwoRadicalIn ⊤ Q := by
  intro hrad
  obtain ⟨t, htT, htP⟩ := ex_sound hvT he
  have hT2 : IsPGroup 2 ↥(subP T m hT) := isPGroup_of_iff (fun _ => Iff.rfl) h4
  have hTN : subP T m hT ≤ Subgroup.normalizer (Q : Set A7) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hQ, hQ]
    refine ⟨fun hx => conj_sound hc hs hx, fun hx => ?_⟩
    have := conj_sound hc ((subP T m hT).inv_mem hs) hx
    simpa [mul_assoc] using this
  have hnormal : ((subP T m hT).subgroupOf (⊤ ⊓ Subgroup.normalizer (Q : Set A7))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (le_inf le_top hTN)]
    intro s g hs hg
    have hg' : g ∈ Subgroup.normalizer (Q : Set A7) := hg.2
    exact norm_sound hvP hn g (fun x hx => (hQ _).1
      ((Subgroup.mem_normalizer_iff.1 hg' x).1 ((hQ x).2 hx))) hs
  have := (isTwoRadicalIn_iff.1 hrad).2.2.2 _ (le_inf le_top hTN) hT2 hnormal
  exact htP ((hQ t).1 (this htT))

theorem good_of_sub {P n L l W : ℕ} {Q : Subgroup A7} (hQ : ∀ x, x ∈ Q ↔ memP P n (cd x) = true)
    (hvP : validB P n = true) (hL : closedB L l = true) (hvL : validB L l = true)
    (hn : nonabB L l = true) (h3 : threeB L l W = true) (hs : subB P n L l = true)
    (hodd : ∀ k, k * n = l → ¬ 2 ∣ k) : A7Good Q := by
  obtain ⟨a, b, ha, hb, hab⟩ := nonab_sound hvL hn
  have hle : Q ≤ subP L l hL := fun x hx => sub_sound hs ((hQ x).1 hx)
  exact ⟨subP L l hL, simple_sound hL hvL hn h3, ⟨a, ha, b, hb, hab⟩, hle,
    not_dvd_index hle (card_of_iff hvP hQ) (card_subP hL hvL) hodd⟩

theorem good_top (hA7 : IsSimpleGroup A7) {P n : ℕ} {Q : Subgroup A7}
    (hQ : ∀ x, x ∈ Q ↔ memP P n (cd x) = true) (hvP : validB P n = true) (hn : nonabB P n = true)
    (hodd : ∀ k, k * n = 2520 → ¬ 2 ∣ k) : A7Good Q := by
  obtain ⟨a, b, -, -, hab⟩ := nonab_sound hvP hn
  have e : ↥(⊤ : Subgroup A7) ≃* A7 := Subgroup.topEquiv
  exact ⟨⊤, e.isSimpleGroup, ⟨a, Subgroup.mem_top _, b, Subgroup.mem_top _, hab⟩, le_top,
    not_dvd_index le_top (card_of_iff hvP hQ) (by rw [Subgroup.card_top, card_A7]) hodd⟩

theorem exists_conj_le {P : Subgroup A7} (hP : IsPGroup 2 ↥P) :
    ∃ g : A7, ∀ x ∈ P, g⁻¹ * x * g ∈ subP D8 8 ch134003_closed_D8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup A7 := subP D8 8 ch134003_closed_D8 with hD
  have hD2 : IsPGroup 2 ↥D := isPGroup_of_iff (fun _ => Iff.rfl) ch134003_pow4_D8
  have hcardD : Nat.card ↥D = 8 := card_subP _ ch134003_valid_D8
  have hidx : ¬ 2 ∣ D.index := by
    have h := Subgroup.card_mul_index D
    rw [hcardD, card_A7] at h
    omega
  let Dsyl : Sylow 2 A7 := hD2.toSylow hidx
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A7 Dsyl Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup A7) := hPQ hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  have h2 : g⁻¹ * x * g ∈ (Dsyl : Subgroup A7) := by
    simpa [MulAut.smul_def, MulAut.conj_inv_apply] using hxQ
  exact h2

theorem good_le_D8 (hA7 : IsSimpleGroup A7) {Q : Subgroup A7} (hrad : IsTwoRadicalIn ⊤ Q)
    (hQD : Q ≤ subP D8 8 ch134003_closed_D8) : A7Good Q := by
  obtain ⟨m, hm, hb⟩ := lat_sound ch134003_lat ch134003_closed_D8 hQD
  simp only [tenM, List.mem_cons, List.not_mem_nil, or_false] at hm
  have mk := fun {G nG : ℕ} (hs : subB G nG D8 8 = true)
    (h : ∀ k < 8, bitB (maskOf D8 8 G nG) k = true ↔ ∃ x ∈ Q, cd x = fld D8 k) =>
    mem_of_mask ch134003_closed_D8 hQD hs h
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    have hQ := mk ch134003_le_E1 hb
    apply (isTwoRadicalIn_iff.1 hrad).2.1
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk, e⟩ := memP_iff.1 ((hQ x).1 hx)
    obtain rfl : k = 0 := by omega
    rw [Subgroup.mem_bot]
    exact cd_inj (by rw [cd_one, ← e]; exact beq_iff.1 ch134003_one_E1)
  · exact (not_rad (mk ch134003_le_Z1 hb) ch134003_closed_V4 ch134003_valid_Z1 ch134003_valid_V4
      ch134003_pow4_V4 ch134003_conj_Z1 ch134003_norm_Z1 ch134003_ex_Z1 hrad).elim
  · exact (not_rad (mk ch134003_le_Z2 hb) ch134003_closed_Tf ch134003_valid_Z2 ch134003_valid_Tf
      ch134003_pow4_Tf ch134003_conj_Z2 ch134003_norm_Z2 ch134003_ex_Z2 hrad).elim
  · exact (not_rad (mk ch134003_le_Z3 hb) ch134003_closed_Tg ch134003_valid_Z3 ch134003_valid_Tg
      ch134003_pow4_Tg ch134003_conj_Z3 ch134003_norm_Z3 ch134003_ex_Z3 hrad).elim
  · exact (not_rad (mk ch134003_le_Z4 hb) ch134003_closed_V4 ch134003_valid_Z4 ch134003_valid_V4
      ch134003_pow4_V4 ch134003_conj_Z4 ch134003_norm_Z4 ch134003_ex_Z4 hrad).elim
  · exact (not_rad (mk ch134003_le_Z5 hb) ch134003_closed_V4 ch134003_valid_Z5 ch134003_valid_V4
      ch134003_pow4_V4 ch134003_conj_Z5 ch134003_norm_Z5 ch134003_ex_Z5 hrad).elim
  · exact (not_rad (mk ch134003_le_C4 hb) ch134003_closed_D8 ch134003_valid_C4 ch134003_valid_D8
      ch134003_pow4_D8 ch134003_conj_C4 ch134003_norm_C4 ch134003_ex_C4 hrad).elim
  · exact good_of_sub (mk ch134003_le_V4 hb) ch134003_valid_V4 ch134003_closed_A5a
      ch134003_valid_A5a ch134003_nonab_A5a ch134003_three_A5a ch134003_sub_V4
      (fun k hk => by omega)
  · exact good_of_sub (mk ch134003_le_V4' hb) ch134003_valid_V4' ch134003_closed_A5b
      ch134003_valid_A5b ch134003_nonab_A5b ch134003_three_A5b ch134003_sub_V4'
      (fun k hk => by omega)
  · exact good_top hA7 (mk ch134003_le_D8 hb) ch134003_valid_D8 ch134003_nonab_D8
      (fun k hk => by omega)

theorem a7Good (hA7 : IsSimpleGroup A7) (P : Subgroup A7) (hrad : IsTwoRadicalIn ⊤ P) :
    A7Good P := by
  obtain ⟨g, hg⟩ := exists_conj_le (isTwoRadicalIn_iff.1 hrad).2.2.1
  let e : A7 ≃* A7 := (MulAut.conj g⁻¹ : MulAut A7)
  refine good_of_map e (good_le_D8 hA7 (isTwoRadicalIn_top_map e hrad) ?_)
  rintro _ ⟨x, hx, rfl⟩
  simpa [e, MulAut.conj_apply] using hg x hx

end CertificateChecks.KernelA7Rad

end
