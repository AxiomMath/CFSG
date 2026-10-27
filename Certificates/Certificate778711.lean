module

public import CFSG.CGT.Stroth77.Section1SplitInputs
import CFSG.Certificates.Kernel.Stroth77.SplitRest
import Certificates.Kernel.Stroth77.SplitChecks
import Certificates.Kernel.Stroth77.SplitChecksW4
public import Certificates.Data.CFSGNative.Stroth15.GL5

public section

namespace Certificates

open CFSG.KC.Stroth77SP CertificateChecks.KernelSplit778711

open CFSG.CGT.Stroth77 Equiv in
theorem certificate778711 : (Nat.card Tsp = 256)
    ∧ (Nat.card Asp = 32)
    ∧ (Nat.card Esp = 16)
    ∧ (∀ a ∈ Asp, ∀ b ∈ Asp, a * b = b * a)
    ∧ (∀ a ∈ Asp, a * a = 1)
    ∧ (∀ B : Subgroup Msp, B ≤ Tsp → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) → Nat.card B = 32 →
        B = Asp)
    ∧ (∀ s ∈ Tsp, (∀ a ∈ Asp, s * a = a * s) → s ∈ Asp)
    ∧ (∀ s ∈ AEsp, (s ∈ Esp ↔ s * s = 1 ∧ (s ∈ Asp → ∀ z ∈ AEsp, s * z = z * s) ∧
        (s ∉ Asp → ∃ z ∈ AEsp, z ∉ Asp ∧ s⁻¹ * z ∉ Asp ∧ z * z = 1 ∧ s * z = z * s)))
    ∧ (spUV * spX1 * spUV⁻¹ = spPhi (GL5.r0 GL5.uvC) ∧
        spUV * spY1 * spUV⁻¹ = spPhi (GL5.r1 GL5.uvC) ∧
        spUV * spX * spUV⁻¹ = spPhi (GL5.r2 GL5.uvC) ∧
        spUV * spY * spUV⁻¹ = spPhi (GL5.r3 GL5.uvC) ∧
        spUV * spW * spUV⁻¹ = spPhi (GL5.r4 GL5.uvC))
    ∧ (spT * spX1 * spT⁻¹ = spPhi (GL5.r0 GL5.tC) ∧ spT * spY1 * spT⁻¹ = spPhi (GL5.r1 GL5.tC) ∧
        spT * spX * spT⁻¹ = spPhi (GL5.r2 GL5.tC) ∧ spT * spY * spT⁻¹ = spPhi (GL5.r3 GL5.tC) ∧
        spT * spW * spT⁻¹ = spPhi (GL5.r4 GL5.tC))
    ∧ (spU * spX1 * spU⁻¹ = spPhi (GL5.r0 GL5.uC) ∧ spU * spY1 * spU⁻¹ = spPhi (GL5.r1 GL5.uC) ∧
        spU * spX * spU⁻¹ = spPhi (GL5.r2 GL5.uC) ∧ spU * spY * spU⁻¹ = spPhi (GL5.r3 GL5.uC) ∧
        spU * spW * spU⁻¹ = spPhi (GL5.r4 GL5.uC))
    ∧ (spRho * spX1 * spRho⁻¹ = spPhi (GL5.r0 GL5.rhoC) ∧
        spRho * spY1 * spRho⁻¹ = spPhi (GL5.r1 GL5.rhoC) ∧
        spRho * spX * spRho⁻¹ = spPhi (GL5.r2 GL5.rhoC) ∧
        spRho * spY * spRho⁻¹ = spPhi (GL5.r3 GL5.rhoC) ∧
        spRho * spW * spRho⁻¹ = spPhi (GL5.r4 GL5.rhoC))
    ∧ (∀ s ∈ Tsp, ∃ d ∈ Dsp, s * d⁻¹ ∈ Asp)
    ∧ (Nat.card ↥(Tsp ⊓ (Perm.sign.comp θsp).ker) = 128)
    ∧ (∀ z ∈ Tsp ⊓ (Perm.sign.comp θsp).ker, z * z = 1 →
        ∃ m : Msp, ∃ r, r < 16 ∧ m * z * m⁻¹ = spPhi r)
    ∧ (∀ a ∈ Asp, ∃ r, r < 32 ∧ spPhi r = a) :=
  ⟨card_Tsp ch778711_tab, card_Asp ch778711_tab ch778711_cl ch778711_a,
    card_Esp ch778711_tab ch778711_cl,
    fun _ ha _ hb => Asp_comm ch778711_tab ch778711_cl ch778711_a ha hb,
    fun _ ha => Asp_sq ch778711_tab ch778711_cl ch778711_a ha,
    Asp_unique ch778711_tab ch778711_cl ch778711_a ch778711_red ch778711_sg,
    fun _ hs h => mem_Asp_of_commute ch778711_tab ch778711_cl ch778711_a hs h,
    fun _ hs => mem_Esp_char ch778711_tab ch778711_cl ch778711_a ch778711_echar hs,
    act_spUV ch778711_tab ch778711_uv, act_spT ch778711_tab ch778711_t,
    act_spU ch778711_tab ch778711_u, act_spRho ch778711_tab ch778711_rho,
    fun _ hs => exists_mem_Dsp ch778711_tab ch778711_cl ch778711_a ch778711_ad hs,
    card_S1 ch778711_tab,
    fun _ hz hz2 => exists_conj_W4 ch778711_tab ch778711_w4 ch778711_s1 hz hz2,
    fun _ ha => exists_spPhi_eq ch778711_tab ch778711_cl ch778711_a ha⟩

end Certificates
