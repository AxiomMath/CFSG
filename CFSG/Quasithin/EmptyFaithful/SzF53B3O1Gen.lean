module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1Alg

public section

namespace CFSG.Quasithin.F53B3.O1

open scoped commutatorElement

variable {G : Type} [Group G]

theorem conj_mem_sup {A B W : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ W)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ W) : ∀ w ∈ A ⊔ B, g * w * g⁻¹ ∈ W := by
  have : A ⊔ B ≤ W.comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  intro w hw
  exact this hw

theorem gen_of_comm {F Fp V Z Zμ : Subgroup G} (hFpF : Fp ≤ F)
    (hFpn : ∀ g ∈ F, ∀ f ∈ Fp, g * f * g⁻¹ ∈ Fp) (hFV : F ≤ Subgroup.normalizer (V : Set G))
    (hFZ : F ≤ Subgroup.normalizer (Z : Set G)) (hZV : Z ≤ V) (hZμV : Zμ ≤ V)
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {s : G} (hsF : s ∈ F)
    (hcos : ∀ g ∈ F, g ∈ Fp ∨ g * s⁻¹ ∈ Fp) (hsZ : ∀ z ∈ Zμ, s * z * s⁻¹ * z⁻¹ ∈ Z)
    (hV : ∀ N : Subgroup G, (∀ g ∈ F, ∀ z ∈ Zμ, g * z * g⁻¹ ∈ N) → V ≤ N)
    (hZμ : Zμ ≤ ⁅V, F⁆) : V ≤ ⁅V, Fp⁆ ⊔ Z := by
  set W := ⁅V, Fp⁆ ⊔ Z with hW
  have hFpN : F ≤ Subgroup.normalizer (Fp : Set G) := fun g hg =>
    mem_normalizer_of_conj (hFpn g hg) (by simpa using hFpn g⁻¹ (F.inv_mem hg))
  have hFc : F ≤ Subgroup.normalizer ((⁅V, Fp⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hFV hFpN
  have hcV : ⁅V, Fp⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv f hf
    have hfv : f * v⁻¹ * f⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hFV (hFpF hf)) v⁻¹).mp (V.inv_mem hv)
    have e : ⁅v, f⁆ = v * (f * v⁻¹ * f⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem hv hfv
  have hWV : W ≤ V := sup_le hcV hZV
  have hA : ∀ g ∈ F, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg
    refine conj_mem_sup (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hFc hg) a).mp ha)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hFZ hg) b).mp hb)
  have hB1 : ∀ f ∈ Fp, ∀ z ∈ Zμ, f * z * f⁻¹ * z⁻¹ ∈ W := by
    intro f hf z hz
    have h1 : ⁅z, f⁆ ∈ ⁅V, Fp⁆ := Subgroup.commutator_mem_commutator (hZμV hz) hf
    have h2 := (⁅V, Fp⁆).inv_mem h1
    have e : (⁅z, f⁆)⁻¹ = f * z * f⁻¹ * z⁻¹ := by simp only [commutatorElement_def]; group
    rw [e] at h2
    exact Subgroup.mem_sup_left h2
  have hB : ∀ g ∈ F, ∀ z ∈ Zμ, g * z * g⁻¹ * z⁻¹ ∈ W := by
    intro g hg z hz
    rcases hcos g hg with h | h
    · exact hB1 g h z hz
    · have hf : g * s⁻¹ ∈ F := F.mul_mem hg (F.inv_mem hsF)
      have h1 := hB1 _ h z hz
      have h2 : (g * s⁻¹) * (s * z * s⁻¹ * z⁻¹) * (g * s⁻¹)⁻¹ ∈ W := by
        have hz2 : s * z * s⁻¹ * z⁻¹ ∈ Z := hsZ z hz
        have := (Subgroup.mem_normalizer_iff.mp (hFZ hf) _).mp hz2
        exact Subgroup.mem_sup_right this
      have e : g * z * g⁻¹ * z⁻¹ =
          ((g * s⁻¹) * (s * z * s⁻¹ * z⁻¹) * (g * s⁻¹)⁻¹) *
            ((g * s⁻¹) * z * (g * s⁻¹)⁻¹ * z⁻¹) := by group
      rw [e]
      exact W.mul_mem h2 h1
  let T : Subgroup G :=
    { carrier := {v | v ∈ V ∧ ∀ g ∈ F, g * v * g⁻¹ * v⁻¹ ∈ W}
      one_mem' := ⟨V.one_mem, fun g _ => by simp⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨V.mul_mem ha.1 hb.1, fun g hg => ?_⟩
        have h1 := ha.2 g hg
        have h2 := hb.2 g hg
        have hc : a * (g * b * g⁻¹ * b⁻¹) = (g * b * g⁻¹ * b⁻¹) * a :=
          hVc a ha.1 _ (hWV h2)
        have e1 : a * (g * b * g⁻¹ * b⁻¹) * a⁻¹ = g * b * g⁻¹ * b⁻¹ := by rw [hc]; group
        have e : g * (a * b) * g⁻¹ * (a * b)⁻¹ =
            (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e, e1]
        exact W.mul_mem h1 h2
      inv_mem' := fun {a} ha => by
        refine ⟨V.inv_mem ha.1, fun g hg => ?_⟩
        have h1 := ha.2 g hg
        have hc : Commute a (g * a * g⁻¹ * a⁻¹) := hVc a ha.1 _ (hWV h1)
        have e : g * a⁻¹ * g⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a := by group
        have e2 : a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a = (g * a * g⁻¹ * a⁻¹)⁻¹ := by
          calc a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * a = a⁻¹ * ((g * a * g⁻¹ * a⁻¹)⁻¹ * a) := by group
            _ = a⁻¹ * (a * (g * a * g⁻¹ * a⁻¹)⁻¹) := by rw [hc.inv_right.eq]
            _ = (g * a * g⁻¹ * a⁻¹)⁻¹ := by group
        rw [e, e2]
        exact W.inv_mem h1 }
  have hZμT : ∀ g ∈ F, ∀ z ∈ Zμ, g * z * g⁻¹ ∈ T := by
    intro h hh z hz
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hFV hh) z).mp (hZμV hz), fun g hg => ?_⟩
    have hg' : h⁻¹ * g * h ∈ F := F.mul_mem (F.mul_mem (F.inv_mem hh) hg) hh
    have h1 := hA h hh _ (hB _ hg' z hz)
    have e : g * (h * z * h⁻¹) * g⁻¹ * (h * z * h⁻¹)⁻¹ =
        h * ((h⁻¹ * g * h) * z * (h⁻¹ * g * h)⁻¹ * z⁻¹) * h⁻¹ := by group
    rw [e]
    exact h1
  have hVT : V ≤ T := hV T hZμT
  have hD : ⁅V, F⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro v hv g hg
    have h1 := (hVT hv).2 g hg
    have h2 := W.inv_mem h1
    have e : (g * v * g⁻¹ * v⁻¹)⁻¹ = ⁅v, g⁆ := by simp only [commutatorElement_def]; group
    rwa [e] at h2
  have hE : Zμ ≤ W := hZμ.trans hD
  exact hV W fun g hg z hz => hA g hg z (hE hz)

end CFSG.Quasithin.F53B3.O1
