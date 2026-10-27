module

public import CFSG.Quasithin.H13.GoldschmidtU43BA
public import CFSG.Quasithin.H13.GoldschmidtU43BElemN

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem conj_inv_mem_of_maps [Finite G] {S : Set G} {g : G} (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) :
    ∀ x ∈ S, g⁻¹ * x * g ∈ S := by
  classical
  let φ : ↥S → ↥S := fun v => ⟨g * v * g⁻¹, h v v.2⟩
  have hinj : Function.Injective φ := by
    intro v v' hvv
    have : g * (v : G) * g⁻¹ = g * (v' : G) * g⁻¹ := congrArg Subtype.val hvv
    exact Subtype.ext (by simpa using this)
  intro x hx
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨x, hx⟩
  have h1 : g * (v : G) * g⁻¹ = x := congrArg Subtype.val hv
  have h2 : g⁻¹ * x * g = v := by rw [← h1]; group
  rw [h2]
  exact v.2

namespace Swap

variable {z t w a : G}

theorem centralizer_E [Finite G] (s : Swap z t w) (ha : Good z t a) :
    Subgroup.centralizer (Eg z t w a : Set G) = Eg z t w a := by
  apply le_antisymm
  · intro x hx
    have hxz : x ∈ Hz z := by
      rw [Hz, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hx z z_mem_Eg).symm
    rw [← s.centralizer_A0 ha]
    exact ⟨hxz, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hx y (s.A0_le_E ha hy)⟩
  · intro x hx
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => (s.Eg_comm_sq ha hx hy).1.symm

theorem mem_normalizer_Eg_of [Finite G] (s : Swap z t w) (ha : Good z t a) {g : G}
    (hg : g ∈ Hz z) (hpres : ∀ x ∈ A0 s ha, g * x * g⁻¹ ∈ A0 s ha) :
    g ∈ Subgroup.normalizer (Eg z t w a : Set G) := by
  have hinv := conj_inv_mem_of_maps hpres
  refine mem_normalizer_of_forward fun y hy => ?_
  rw [← s.centralizer_A0 ha] at hy ⊢
  refine ⟨mul_mem (mul_mem hg hy.1) ((Hz z).inv_mem hg), Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro x hx
  have h1 := Subgroup.mem_centralizer_iff.mp hy.2 _ (hinv x hx)
  calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    _ = (g * y * g⁻¹) * x := by group

theorem maps_A0_of_mem_normalizer [Finite G] (s : Swap z t w) (ha : Good z t a) {g : G}
    (hg : g ∈ Hz z) (hn : g ∈ Subgroup.normalizer (Eg z t w a : Set G)) {x : G}
    (hx : x ∈ A0 s ha) : g * x * g⁻¹ ∈ A0 s ha := by
  refine s.E_inf_U_le_A0 ha ((Subgroup.mem_normalizer_iff.mp hn x).mp (s.A0_le_E ha hx)) ?_
  obtain ⟨hxU, -⟩ := hx
  exact (Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z hg) x).mp hxU

theorem vapp_act (s : Swap z t w) {g u : G} (hg : g ∈ Hz z) (hu : u ∈ Uz z) :
    vapp (s.hyp.act ⟨g, hg⟩) (Multiplicative.toAdd (s.hyp.θ ⟨u, hu⟩)) =
      Multiplicative.toAdd (s.hyp.θ ⟨g * u * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp (Hz_le_normalizer z hg) u).mp hu⟩) := by
  unfold vapp
  rw [ofAdd_toAdd, s.hyp.act_θ]
  rfl

theorem act_mem_StabA [Finite G] (s : Swap z t w) (ha : Good z t a) {g : G} (hg : g ∈ Hz z)
    (hn : g ∈ Subgroup.normalizer (Eg z t w a : Set G)) :
    s.hyp.act ⟨g, hg⟩ ∈ StabA s.tauV (s.alphaV ha) := by
  refine ⟨s.hyp.act_mem_Oq _, ?_, ?_⟩
  · have := s.maps_A0_of_mem_normalizer ha hg hn (s.t_mem_A0 ha)
    obtain ⟨hx, hA⟩ := this
    have e := s.vapp_act hg s.ht.1
    show Aset _ _ (vapp (s.hyp.act ⟨g, hg⟩) (Multiplicative.toAdd (s.hyp.θ ⟨t, s.ht.1⟩)))
    rw [e]
    exact hA
  · have := s.maps_A0_of_mem_normalizer ha hg hn (s.a_mem_A0 ha)
    obtain ⟨hx, hA⟩ := this
    have e := s.vapp_act hg ha.mem.1
    show Aset _ _ (vapp (s.hyp.act ⟨g, hg⟩) (Multiplicative.toAdd (s.hyp.θ ⟨a, ha.mem.1⟩)))
    rw [e]
    exact hA

end Swap

end CFSG.Quasithin.H13.U43
