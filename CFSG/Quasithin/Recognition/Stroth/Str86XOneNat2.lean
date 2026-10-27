module

public import CFSG.Quasithin.Recognition.F112WChief
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Recognition.GoldschmidtF112RLeaves
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_noncentral_chiefStep {H U N : Subgroup G} {c : ℕ}
    (hser : IsChiefSeriesFrom H U N c) (hc : c = 1) :
    ∃ L N' : Subgroup G, IsChiefStep H U L N' ∧ ¬ IsCentralStep H L N' ∧ N' ≤ N := by
  induction hser with
  | bot => omega
  | central hstep hcent hser ih =>
      obtain ⟨L, N', hstep', hnc, hle⟩ := ih hc
      exact ⟨L, N', hstep', hnc, hle.trans hstep.2.2.1.le⟩
  | noncentral hstep hnc hser ih =>
      exact ⟨_, _, hstep, hnc, le_rfl⟩

theorem inf_le_lower_of_noncentral {H X L N Z : Subgroup G} (hXH : X ≤ H)
    (hstep : IsChiefStep H X L N) (hnc : ¬ IsCentralStep H L N)
    (hZX : Z ≤ X) (hZH : H ≤ Subgroup.normalizer (Z : Set G))
    (hZcentral : ∀ h ∈ H, ∀ z ∈ Z, h * z = z * h) :
    Z ⊓ N ≤ L := by
  classical
  have hZnorm : IsNormalIn H X Z :=
    F112W.isNormalIn_of_le_normalizer hZX hZH
  have hKnorm : IsNormalIn H X (Z ⊓ N) := F112W.isNormalIn_inf hZnorm hstep.1
  have hsupnorm : IsNormalIn H X (L ⊔ (Z ⊓ N)) :=
    F112W.isNormalIn_sup hstep.2.1 hKnorm
  have hLle : L ≤ L ⊔ (Z ⊓ N) := le_sup_left
  have hleN : L ⊔ (Z ⊓ N) ≤ N := sup_le hstep.2.2.1.le inf_le_right
  rcases hstep.2.2.2 _ hsupnorm hLle hleN with h | h
  · exact le_sup_right.trans (le_of_eq h)
  · exfalso
    apply hnc
    have hKleN : Z ⊓ N ≤ N := inf_le_right
    have hKN : Z ⊓ N ≤ Subgroup.normalizer (L : Set G) :=
      hKleN.trans (hstep.1.1.trans (hXH.trans
        (D14.le_normalizer_of_isNormalIn (H := H) (U := X) hstep.2.1)))
    intro g hg x hx
    obtain ⟨l, hl, k, hk, rfl⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hKN).mp (by rw [h]; exact hx)
    have hgl : g * l * g⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp
        (D14.le_normalizer_of_isNormalIn (H := H) (U := X) hstep.2.1 hg) l).mp hl
    have hcomm : g * k = k * g := hZcentral g hg k hk.1
    have hgk : g * k * g⁻¹ = k := by
      rw [hcomm]
      group
    have heq : g * (l * k) * g⁻¹ * (l * k)⁻¹ =
        (g * l * g⁻¹) * l⁻¹ := by
      rw [show g * (l * k) * g⁻¹ * (l * k)⁻¹ =
        (g * l * g⁻¹) * (g * k * g⁻¹) * k⁻¹ * l⁻¹ by group]
      rw [hgk]
      group
    rw [heq]
    exact L.mul_mem hgl (L.inv_mem hl)

end CFSG.Quasithin.Stroth
