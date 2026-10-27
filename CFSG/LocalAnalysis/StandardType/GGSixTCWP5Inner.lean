module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcTwE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Upper

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open

section Inner

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem GGTCHyp.inner_twE6
    {ψ : (ggU .twistedE6 n f).K →* X} (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x)
    (hp3 : p ≠ 3 ∨ ¬ 3 ∣ 2 ^ f + 1) :
    ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X) := by
  intro b hb
  have hcN : b ∈ Subgroup.normalizer (G₀ : Set X) := h.b_norm hb
  have hcp : b ^ p = 1 := h.b_elem.2 b hb
  have hci := h.b_diag b hb
  have hker := h.ker
  have hperf := h.perfect
  have hf : 1 ≤ f := h.adm.2.1
  have hrange := h.range
  have hcN' : b ∈ Subgroup.normalizer (ψ.range : Set X) := hrange.symm ▸ hcN
  have hperf' : commutator ↥ψ.range = ⊤ := hrange.symm ▸ hperf
  obtain ⟨π, hπ, hkerπ, -, hπval⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkπ : ψ.ker ≤ π.ker := hker.trans hkerπ.ge
  obtain ⟨α, hαD, hα⟩ :=
    LayerSixE.exists_induces_twistedE6 hf hπval ψ hker hkπ hcN' hci
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hcN' p
    rw [hcp] at h1
    exact LayerSixE.GGInduces.unique hπ (Subgroup.one_mem _) h1 (LayerSixE.GGInduces.one hkπ)
  have hout : ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1) :=
    fun ⟨h1, h2⟩ => hp3.elim (fun h => h h1) (fun h => h h2)
  have hinn :=
    ggTwE6InndiagOrdPInnerInput_holds f p hf h.prime h.ne_two hout α hαD hαp
  obtain ⟨y, rfl⟩ := hinn
  obtain ⟨w, rfl⟩ := hπ y
  have hwN : ψ w⁻¹ ∈ Subgroup.normalizer (ψ.range : Set X) :=
    Subgroup.le_normalizer ⟨w⁻¹, rfl⟩
  have hd := hα.mul hwN (LayerSixE.GGInduces.psi hkπ w⁻¹)
  have hconj : MulAut.conj (π w) * MulAut.conj (π w⁻¹) = 1 := by
    rw [← map_mul (MulAut.conj), ← map_mul π, mul_inv_cancel, map_one, map_one]
  have hd1 : LayerSixE.GGInduces π ψ (b * ψ w⁻¹) 1 := hconj ▸ hd
  have hcd :=
    OrdPInnerExc.mem_centralizer_of_induces_one hkerπ.le hperf' (mul_mem hcN' hwN) hd1
  exact ⟨ψ w⁻¹, hrange ▸ ⟨w⁻¹, rfl⟩, hrange ▸ hcd⟩

end Inner

end CFSG.StandardType.TableCRes

end
