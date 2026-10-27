module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxStep6
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxFamily
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxBasic
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxNotG2
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMPrimeInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGLevTwoMain
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobLin

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem reflGen_of_routeCfg {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) := by
  have h' := ggSecFiveRouteCfg'_of_routeCfg h
  simpa only [GGSecFiveWeylCase'] using h'.2.1


private lemma qTwoRM_eps_zpowers_eq {x b : G} {p : ℕ} (hp : p.Prime)
    (hox : orderOf x = p) (hbx : b ∈ Subgroup.zpowers x) (hb1 : b ≠ 1) :
    x ∈ Subgroup.zpowers b := by
  have hdvd : orderOf b ∣ p := by rw [← hox]; exact orderOf_dvd_of_mem_zpowers hbx
  have hordb : orderOf b = p :=
    ((Nat.dvd_prime hp).mp hdvd).resolve_left (fun h => hb1 (orderOf_eq_one_iff.mp h))
  have hle : Subgroup.zpowers b ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hbx
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hox]
  have hcardb : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hordb]
  have heq : Subgroup.zpowers b = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardx, hcardb])
  exact heq.symm ▸ Subgroup.mem_zpowers x

private theorem nbr_le_ainf {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    ggAutomizer K Bs ≤ ggAInf p B Bs x L D J := by
  rw [ggAInf]
  refine le_sup_of_le_right ?_
  exact (le_iSup (fun _ : GGNbr p B x D J y K => ggAutomizer K Bs) hnbr).trans
    ((le_iSup (fun K' : Subgroup G =>
        ⨆ (_ : GGNbr p B x D J y K'), ggAutomizer K' Bs) K).trans
      (le_iSup (fun y' => ⨆ K' : Subgroup G,
        ⨆ (_ : GGNbr p B x D J y' K'), ggAutomizer K' Bs) y))

theorem qTwo_ainf_fixes_x {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m : ℕ} (hLM : QTwoLocalModel m Bs L x)
    (hC : ¬ ∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1) :
    ∀ φ ∈ ggAInf 3 B Bs x L D J, φ ⟨x, hLM.mem⟩ = ⟨x, hLM.mem⟩ := by
  have hle : ggAutomizer L Bs ≤ ggAInf 3 B Bs x L D J := le_sup_left
  push Not at hC
  obtain ⟨b, hb, hb1⟩ := hC
  have hbmem : (b : G) ∈ Subgroup.zpowers x := hLM.fixed b fun φ hφ => hb φ (hle hφ)
  have hbG1 : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hx1 : x ≠ 1 := by
    intro hx
    apply hbG1
    have hbot : Subgroup.zpowers x = ⊥ := by rw [hx, Subgroup.zpowers_one_eq_bot]
    rw [hbot] at hbmem
    simpa using hbmem
  have hxpow : x ^ 3 = 1 := hLM.elemAb.2 x hLM.mem
  have hox : orderOf x = 3 := orderOf_eq_prime hxpow hx1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (qTwoRM_eps_zpowers_eq Nat.prime_three hox hbmem hbG1)
  intro φ hφ
  have hφb : φ b = b := hb φ hφ
  have hbn : b ^ n = (⟨x, hLM.mem⟩ : ↥Bs) := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    exact hn
  calc φ ⟨x, hLM.mem⟩ = φ (b ^ n) := by rw [← hbn]
    _ = (φ b) ^ n := map_zpow φ b n
    _ = b ^ n := by rw [hφb]
    _ = ⟨x, hLM.mem⟩ := hbn

theorem qTwo_rm_fixed {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m : ℕ} (hLM : QTwoLocalModel m Bs L x)
    (hC : ¬ ∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1) :
    ∀ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' → ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
  have hfix := qTwo_ainf_fixes_x hcfg hLM hC
  have hgen := reflGen_of_routeCfg hcfg
  intro y K hnbr
  have hKL : ggAutomizer K Bs ≤ ggAutomizer L Bs := by
    rw [hgen y K hnbr]
    refine (Subgroup.closure_le (K := ggAutomizer L Bs)).mpr ?_
    rintro t ⟨htK, htr⟩
    have htA : t ∈ ggAInf 3 B Bs x L D J := nbr_le_ainf hnbr htK
    exact hLM.direct t (ggRM_ainf_le_induced htA) htr (hfix t htA)
  exact hKL.trans (by rw [ggAutomizerJoin]; exact le_sup_left)


theorem qTwo_witness_main
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m : ℕ} (hm : 5 ≤ m) (hLM : QTwoLocalModel m Bs L x)
    (hW : GGWeylReflectionGroup 3 (ggAInf 3 B Bs x L D J)) :
    GGSecFiveInfWitness 3 B Bs x L D J := by
  have hcfg' := ggSecFiveRouteCfg'_of_routeCfg hcfg
  have hNT : GGNoTransvection 3 Bs := hcfg.1.2.2.2.1
  refine ⟨hW, ?_⟩
  obtain ⟨ι, M, hM, f, hf⟩ := hW
  have hML : GGIsWeylMatrixAD (CoxeterMatrix.A (m - 1)) ∨ GGIsWeylMatrixE (CoxeterMatrix.A (m - 1)) :=
    Or.inl (Or.inl ⟨m - 1, Equiv.refl _, by omega, rfl⟩)
  obtain ⟨𝒮', h𝒮'sub, hcard', heq⟩ :=
    ggSecFiveLevTwoInput'_holds G 3 Bs Nat.prime_three (by decide) hLM.elemAb hNT
      (ggAInf 3 B Bs x L D J) (ggRM_ainf_le_induced)
      ι M hM (ggRM_not_G2 hML hLM.weyl le_sup_left f) f hf
      ⟨x, hLM.mem⟩ (ggAutomizer L Bs) (Fin (m - 1)) (CoxeterMatrix.A (m - 1)) le_sup_left hLM.fixes
      hML hLM.weyl (by rw [hLM.card, Fintype.card_fin]; exact le_of_eq (by congr 1; omega))
      (fun a haA hrefl hfixa _ => hLM.direct a (ggRM_ainf_le_induced haA) hrefl hfixa)
      (GGSecFiveNbrAutFamily 3 B Bs x D J) (by
        intro K hK
        obtain ⟨y, K₀, hNK, rfl⟩ := hK
        refine ⟨?_, ?_⟩
        · exact (le_iSup_of_le y (le_iSup_of_le K₀ (le_iSup_of_le hNK
            (le_rfl : ggAutomizer K₀ Bs ≤ ggAutomizer K₀ Bs)))).trans le_sup_right
        · exact hcfg'.2.1 y K₀ hNK)
  obtain ⟨𝒦', h𝒦', hjoin'⟩ := ggRM_nbrs_of_family 𝒮' h𝒮'sub hcard'
  refine ⟨𝒦', h𝒦', ?_⟩
  calc ggAutomizerJoin L Bs 𝒦'
      = ggAutomizer L Bs ⊔ ⨆ S ∈ 𝒮', S := hjoin'
    _ = ggAutomizer L Bs ⊔ ⨆ S ∈ GGSecFiveNbrAutFamily 3 B Bs x D J, S := heq.symm
    _ = ggAInf 3 B Bs x L D J := ggRM_ainf_eq_sup.symm

theorem qTwo_rm2
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m : ℕ} (hm : 5 ≤ m) (hLM : QTwoLocalModel m Bs L x)
    (hWeyl : (∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1) →
      GGWeylReflectionGroup 3 (ggAInf 3 B Bs x L D J)) :
    ∀ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' → ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
  by_cases hC : ∀ b : ↥Bs, (∀ φ ∈ ggAInf 3 B Bs x L D J, φ b = b) → b = 1
  · exact ggRM_of_witness hcfg.2.2.2 (qTwo_witness_main hcfg hm hLM (hWeyl hC))
  · exact qTwo_rm_fixed hcfg hLM hC

theorem qTwoGlobLin_rm2
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod 3) V} {Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U)}
    {ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {m N : ℕ} (hm : 5 ≤ m) (hN1 : m + 1 ≤ N) (hN2 : N ≤ m + 2)
    (hA : GGWeylOfType 3 (CoxeterMatrix.A (N - 1)) (ggAutomizerJoin L Bs 𝒦))
    (hLM : QTwoLocalModel m Bs L x)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hdim : Module.finrank (ZMod 3) U = m ∨ Module.finrank (ZMod 3) U + 1 = m)
    (hFam : ZS.Family 3 Abar) :
    ∀ (y : G) (K' : Subgroup G), GGNbr 3 B x D J y K' →
      ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
  qTwo_rm2 hcfg hm hLM (fun _ =>
    qTwoGlobLin_ainf_weyl hcfg hm hN1 hN2 hA hLM hD hdim hFam)

end CFSG.StandardType.QTwo

end
