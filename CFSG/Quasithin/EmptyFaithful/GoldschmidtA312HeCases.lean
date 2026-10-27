module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsHat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsExtra
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsO2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import Certificates.Certificate3168
public import Certificates.Certificate4033
public import Certificates.Certificate4141
public import Certificates.Certificate4167
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender

public section

namespace CFSG.Quasithin.A312He

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.A312Words
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin

theorem he_hat3_cert :
    HeHatFacts (heCtx.Y 3) :=
  Certificates.certificate4167.1

theorem he_hat4_cert :
    HeHatFacts (heCtx.Y 4) :=
  Certificates.certificate4167.2.1

theorem he_ext7_cert :
    HeExtFacts (heCtx.Y 7) :=
  Certificates.certificate4167.2.2

theorem he_shape_hat3
    {S B : Subgroup CFSG.Sporadic.He.J} (hS : IsPGroup 2 S) (hB : B ∈ lFamily S)
    (hY : B ⊔ S = heCtx.Y 3) :
    IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6))) := by
  have hc : Nat.card (heCtx.Y 3) = 138240 := by
    rw [he_member_card 3 (by norm_num)]; rfl
  obtain ⟨ol, t, hid, pt, hpt, hperm, y1, y2, hy1, hy2, h1, h2, vl, hvol, hVnorm, hvc, hvsq, hvfix,
    hVcard⟩ := he_hat3_cert
  exact isExt_hat_of_data hS hB hY hid hc pt hpt hperm y1 y2 hy1 hy2 h1 h2 vl hvol hVnorm hvc hvsq
    hvfix hVcard

theorem he_shape_hat4
    {S B : Subgroup CFSG.Sporadic.He.J} (hS : IsPGroup 2 S) (hB : B ∈ lFamily S)
    (hY : B ⊔ S = heCtx.Y 4) :
    IsExt ↥B (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6))) := by
  have hc : Nat.card (heCtx.Y 4) = 138240 := by
    rw [he_member_card 4 (by norm_num)]; rfl
  obtain ⟨ol, t, hid, pt, hpt, hperm, y1, y2, hy1, hy2, h1, h2, vl, hvol, hVnorm, hvc, hvsq, hvfix,
    hVcard⟩ := he_hat4_cert
  exact isExt_hat_of_data hS hB hY hid hc pt hpt hperm y1 y2 hy1 hy2 h1 h2 vl hvol hVnorm hvc hvsq
    hvfix hVcard

theorem card_pCore_of_pCoreOf' {Γ : Type} [Group Γ] {Y : Subgroup Γ} {k : ℕ}
    (h : Nat.card (CFSG.Open.pCoreOf 2 Y) = k) : Nat.card (CFSG.pCore 2 ↥Y) = k := by
  have h1 : CFSG.Open.pCoreOf 2 Y = (CFSG.pCore 2 ↥Y).map Y.subtype := rfl
  rwa [h1, Subgroup.card_map_of_injective Y.subtype_injective] at h

theorem he_o2_seven :
    Nat.card (CFSG.pCore 2 ↥(heCtx.Y 7)) = 2 ^ 7 := by
  obtain ⟨m, hm, h1, h2, -⟩ := he_row 7 (by norm_num)
  have hc : Nat.card (heCtx.Y 7) = 21504 := by
    rw [he_member_card 7 (by norm_num)]; rfl
  simp only [heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (exfalso; simp only at h1; omega)
    | exact card_pCore_of_pCoreOf' (by simpa using h2)

theorem isExt_extra_of_facts {Γ : Type} [Group Γ] [Finite Γ] {S B Y Y₃ W : Subgroup Γ}
    {ol : List Γ} (hB : B ∈ lFamily S) (hY : B ⊔ S = Y) (hle : Y₃ ≤ Y)
    (hc : Nat.card Y = 2 ^ 10 * 3 * 7) (hc₃ : Nat.card Y₃ = 2 ^ 10 * 3)
    (hP : Nat.card (CFSG.pCore 2 ↥Y) = 2 ^ 7) (hdata : IdxTwoData Y ol 1) (hWY : W ≤ Y)
    (hWn : ∀ g ∈ ol, ∀ v ∈ W, g⁻¹ * v * g ∈ W) (hWcard : Nat.card W = 2 ^ 7)
    (hExt : IsExtraspecial2 3 W) :
    IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) := by
  have hWn' : ∀ g ∈ ol ++ [1], ∀ v ∈ W, g⁻¹ * v * g ∈ W := by
    intro g hg v hv
    rcases List.mem_append.mp hg with hg | hg
    · exact hWn g hg v hv
    · rw [List.mem_singleton.mp hg, inv_one, one_mul, mul_one]
      exact hv
  have hq : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → Nat.card (↥Y ⧸ N) ≤ 1 :=
    fun N _ hp => card_quot_le_one hdata rfl N hp
  obtain ⟨hpsl, ⟨e⟩⟩ := CFSG.Quasithin.A312Ru.modO2_psl32_gen (e := 10) (k := 7) hB hY
    (by norm_num) hle hc hc₃ hP hq
  have hpc : CFSG.pCore 2 ↥Y = W.subgroupOf Y :=
    pCore_eq_subgroupOf hWY (idxTwo_conj_mem hdata hWn') hWcard hP
  have hExtY : IsExtraspecial2 3 ↥(CFSG.pCore 2 ↥Y) := by
    rw [hpc]
    exact IsExtraspecial2.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hWY).symm hExt
  exact ⟨CFSG.pCore 2 ↥B, inferInstance, IsExtraspecial2.of_mulEquiv e.symm hExtY, hpsl⟩

theorem he_shape_ext7
    {S B : Subgroup CFSG.Sporadic.He.J} (hB : B ∈ lFamily S) (hY : B ⊔ S = heCtx.Y 7) :
    IsExt ↥B (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) := by
  have hc : Nat.card (heCtx.Y 7) = 2 ^ 10 * 3 * 7 := by
    rw [he_member_card 7 (by norm_num)]; rfl
  have hc8 : Nat.card (heCtx.Y 8) = 2 ^ 10 * 3 := by
    rw [he_member_card 8 (by norm_num)]; rfl
  have hle : heCtx.Y 8 ≤ heCtx.Y 7 :=
    (he_Y_le_iff (by norm_num) (by norm_num)).mpr (by decide)
  obtain ⟨ol, W, hdata, hWY, hWn, hWcard, hExt⟩ := he_ext7_cert
  exact isExt_extra_of_facts hB hY hle hc hc8 he_o2_seven hdata hWY hWn hWcard hExt

end CFSG.Quasithin.A312He
