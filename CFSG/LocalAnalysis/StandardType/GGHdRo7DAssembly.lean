module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUAssembly

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem d_lin_of_leaves (hN : DNormalizerLeaf) (hF : DFixWeylLeaf) (hU : DReduceULeaf)
    (hV : DReduceVLeaf) (hC : DClassLargeLeaf) (hSm : DLinSmallLeaf) (hKG : GGReflClassLargeInput')
    {p : ℕ} [Fact p.Prime] {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {b : Module.Basis (Fin (n + 1)) (ZMod p) V} {H A : Subgroup (V ≃ₗ[ZMod p] V)}
    (hD : DLinData p n V b H A) : ZS.LinWeyl p H := by
  have hn6 := hD.hn
  have hfixW : (∀ a ∈ H, a (b 0) = b 0) → ZS.LinWeyl p H := fun hfix =>
    hF p hD.hp n hn6 V b H hD.hPH fun a ha =>
      hN p hD.hp n (by omega) V b a (hD.hStab a (hD.hHA ha) (hfix a ha)) (hfix a ha)
  by_cases hspan : ∃ r ∈ H, GGLinRefl r ∧ ¬ ggLinMove r ≤ LinearMap.ker (b.coord 0)
  · by_cases hmove : ∃ a ∈ H, a (b 0) ≠ b 0
    · by_cases hsmall : n = 6 ∨ n = 7
      · exact hSm p n V b H A hD hsmall hspan hmove
      · obtain ⟨hirr, hcard⟩ := hV hN p n V b H A hD hspan hmove
        have hgen : H = Subgroup.closure {r | r ∈ H ∧ GGLinRefl r} := by
          obtain ⟨S, hS, hHS, -⟩ := hD.hgen
          apply le_antisymm
          · conv_lhs => rw [hHS]
            exact Subgroup.closure_mono fun s hs => hS s hs
          · exact (Subgroup.closure_le _).mpr fun r hr => hr.1
        have hfin : Module.finrank (ZMod p) V = n + 1 := by
          rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
        exact hC hKG p hD.hp (n + 1) (by omega) V hfin H hirr hgen hcard
    · exact hfixW fun a ha => by
        by_contra hne
        exact hmove ⟨a, ha, hne⟩
  · exact hfixW (hU p n V b H A hD fun r hr hrf => by
      by_contra hn
      exact hspan ⟨r, hr, hrf, hn⟩)

theorem d_core {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X O J : Subgroup G} {z : G}
    (hNoTVBs : GGNoTransvection p Bs) (hNoTV : NoTVLeaf) (hXD : XDatumGraphLeaf) (hGr : SUGraphLeaf)
    (hDLin : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
      DLinData p n V b H A → ZS.LinWeyl p H)
    (hCLin : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (AL Q A : Subgroup (V ≃ₗ[ZMod p] V)),
      C2LinData p n V b AL Q A → ZS.LinWeyl p (AL ⊔ Q))
    (hDX : GGResXDatum p Bs X) (hDO : GGResXDatum p Bs O)
    (hAJ : (∃ a ∈ ggAutomizer J Bs, ∃ c ∈ ggAutomizer J Bs, a * c ≠ c * a) ∧
      ggAutomizer J Bs ≤ ggAutomizer X Bs ⊓ ggAutomizer O Bs)
    (hM : DModelAt p Bs X z)
    (hstab : ∀ (hz : z ∈ Bs), ∀ ψ ∈ ggAutomizer ⊤ Bs, ψ ⟨z, hz⟩ = ⟨z, hz⟩ →
      ∀ φ ∈ ggAutomizer X Bs, ψ * φ * ψ⁻¹ ∈ ggAutomizer X Bs) :
    GGWeylReflectionGroup p (ggAutomizer X Bs ⊔ ggAutomizer O Bs) := by
  obtain ⟨n, V, _, _, ι, b, hz, hp3, hzb, hmod⟩ := hM
  have hlin : ∀ a ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) ι), a (b 0) = b 0 →
      ∀ s ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι),
        a * s * a⁻¹ ∈ (ggAutomizer X Bs).map (ggLin (p := p) ι) := by
    intro a ha hfix s hs
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hs
    have hψz : ψ ⟨z, hz⟩ = ⟨z, hz⟩ :=
      (ggLin_fix_iff (p := p) ι ψ (⟨z, hz⟩ : ↥Bs)).mpr (by rw [hzb]; exact hfix)
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (hstab hz ψ hψ hψz φ hφ)
  obtain ⟨SX, hSX, hQX, hcX⟩ := hXD G p Bs X hDX V ι
  obtain ⟨SO, hSO, hQO, hcO⟩ := hXD G p Bs O hDO V ι
  have hNoT := hNoTV G p Bs hNoTVBs V ι
  obtain ⟨⟨a, haJ, c, hcJ, hac⟩, hJle⟩ := hAJ
  rcases hmod with ⟨hn, hAX⟩ | ⟨hn, hAX⟩
  · obtain ⟨S, hS, hQ, hconn⟩ := hGr p V _ _ ((ggAutomizer J Bs).map (ggLin (p := p) ι)) SX SO
      hSX hQX hcX hSO hQO hcO (Subgroup.map_mono (hJle.trans inf_le_left))
      (Subgroup.map_mono (hJle.trans inf_le_right))
      ⟨ggLin (p := p) ι a, Subgroup.mem_map_of_mem _ haJ, ggLin (p := p) ι c,
        Subgroup.mem_map_of_mem _ hcJ, fun h => hac (ggLin_injective (p := p) ι (by
          simpa [← map_mul] using h))⟩
    rw [← Subgroup.map_sup] at hS hQ
    have hDat : DLinData p n V b ((ggAutomizer X Bs ⊔ ggAutomizer O Bs).map (ggLin (p := p) ι))
        ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) :=
      { hp := hp3
        hn := hn
        hPH := fun g hg => Subgroup.map_mono le_sup_left ((hAX g).mpr hg)
        hHA := Subgroup.map_mono (sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top))
        hStab := fun g hg hfix s hs => (hAX _).mp (hlin g hg hfix s ((hAX s).mpr hs))
        hNoT := hNoT
        hgen := ⟨S, hS, hQ, hconn⟩ }
    exact ggRC_weylReflGroup_of_linWeyl ι _ (hDLin n V b _ _ hDat)
  · by_cases hle : ggAutomizer O Bs ≤ ggAutomizer X Bs
    · rw [sup_eq_left.mpr hle]
      exact weyl_of_xDatum hDX
    · have ha1 : a ≠ 1 := fun h => hac (by rw [h, one_mul, mul_one])
      have hDat : C2LinData p n V b ((ggAutomizer X Bs).map (ggLin (p := p) ι))
          ((ggAutomizer O Bs).map (ggLin (p := p) ι)) ((ggAutomizer ⊤ Bs).map (ggLin (p := p) ι)) :=
        { hp := hp3
          hn := hn
          hAL := hAX
          hALA := Subgroup.map_mono (ggAutomizer_mono Bs le_top)
          hQA := Subgroup.map_mono (ggAutomizer_mono Bs le_top)
          hStab := fun g hg hfix s hs => (hAX _).mp (hlin g hg hfix s ((hAX s).mpr hs))
          hNoT := hNoT
          hQgen := ⟨SO, hSO, hQO, hcO⟩
          hJ := ⟨ggLin (p := p) ι a, Subgroup.mem_map_of_mem _ (hJle haJ).2,
            Subgroup.mem_map_of_mem _ (hJle haJ).1, fun h => ha1 (ggLin_injective (p := p) ι (by
              simpa using h))⟩
          hnle := fun h => hle (fun g hg => by
            have := h (Subgroup.mem_map_of_mem (ggLin (p := p) ι) hg)
            obtain ⟨g', hg', hgg⟩ := Subgroup.mem_map.mp this
            exact (ggLin_injective (p := p) ι hgg) ▸ hg') }
      exact ggRC_weylReflGroup_of_linWeyl ι _
        (by rw [Subgroup.map_sup]; exact hCLin n V b _ _ _ hDat)

theorem ggResDCorank2Input_of_leaves (hX : GGResXDichotomyInput) (hJ : GGTBJInputR)
    (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hKG : GGReflClassLargeInput')
    (hN : DNormalizerLeaf) (hF : DFixWeylLeaf) (hU : DReduceULeaf) (hV : DReduceVLeaf)
    (hC : DClassLargeLeaf) (hSm : DLinSmallLeaf)
    (hCN : C2NormalizerLeaf) (hCR : C2ReflLeaf)
    (hGr : SUGraphLeaf) (hNoTV : NoTVLeaf) (hXD : XDatumGraphLeaf)
    (hLM : DLModelLeaf) (hLS : DLStabLeaf) (hKM : DKModelLeaf) (hKS : DKStabLeaf)
    (hAJ : DAJLeaf) : GGResDCorank2Input := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hrow
  have hp3 : p = 3 := by
    rcases hrow with ⟨-, -, -, -, -, -, h3, -⟩ | ⟨-, -, -, -, -, -, h3, -⟩ <;> exact h3
  have hDL : GGResXDatum p Bs L := by
    rcases (hX G p B Bs x L D J y K hH).1 with hD | h7
    · exact hD
    · exfalso
      obtain ⟨-, -, -, -, -, -, h7p, -⟩ := h7
      omega
  have hDK : GGResXDatum p Bs K := by
    rcases (hX G p B Bs x L D J y K hH).2 with hD | h7
    · exact hD
    · exfalso
      obtain ⟨-, -, -, -, -, -, h7p, -⟩ := h7
      omega
  have hDLin : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
      DLinData p n V b H A → ZS.LinWeyl p H :=
    fun _ _ _ _ _ _ _ hD => d_lin_of_leaves hN hF hU hV hC hSm hKG hD
  have hCLin : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (AL Q A : Subgroup (V ≃ₗ[ZMod p] V)),
      C2LinData p n V b AL Q A → ZS.LinWeyl p (AL ⊔ Q) :=
    fun _ _ _ _ _ _ _ _ hD => c2_lin_of_leaves hCN hCR c2_join_of_leaves hD
  have hAJ' := hAJ hX hJ hRig hLB G p B Bs x L D J y K hH
    (fun hr => hLM G p B Bs x L D J y K hH hr)
    (fun hr => (hKM hRig hLB G p B Bs x L D J y K hH hr).1) hrow
  rcases hrow with hrow | hrow
  · exact d_core hH.2.2.2.1 hNoTV hXD hGr hDLin hCLin hDL hDK hAJ'
      (hLM G p B Bs x L D J y K hH hrow) fun hx => hLS G p B Bs x L D J y K hH hrow hx
  · obtain ⟨hMK, hcen⟩ := hKM hRig hLB G p B Bs x L D J y K hH hrow
    rw [sup_comm]
    exact d_core hH.2.2.2.1 hNoTV hXD hGr hDLin hCLin hDK hDL
      ⟨hAJ'.1, hAJ'.2.trans (le_of_eq (inf_comm _ _))⟩ hMK
      fun hy => hKS G p B Bs x L D J y K hH hrow hy hcen

end CFSG.StandardType.HdRo7D
