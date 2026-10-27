module

public import CFSG.Quasithin.Vol2.Ch11SecAFactsFlag
public import CFSG.Quasithin.Vol2.Ch11SecAFacts

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Quasithin.Vol2.Ch11.SecA

variable {W : Type*} [Group W] {H P : Subgroup (MulAut W)} {Z U : Subgroup W} {q i : ℕ}

theorem mem_map_aut_iff {n : MulAut W} {u : W} : u ∈ U.map n.toMonoidHom ↔ n⁻¹ u ∈ U := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro hu
    exact ⟨n⁻¹ u, hu, by simp⟩

theorem isFlagW_map (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {n : MulAut W} (hnH : n ∈ H)
    (hnP : n ∈ Subgroup.normalizer (P : Set (MulAut W))) (hU : IsFlagW H P Z q i U) :
    IsFlagW H P Z q i (U.map n.toMonoidHom) := by
  obtain ⟨hZU, hEnd, hidx, hPU⟩ := hU
  have hn' : n⁻¹ ∈ H := H.inv_mem hnH
  have hZn : ∀ z ∈ Z, n⁻¹ z = z := fun z hz => hHZ _ hn' z hz
  have hZn' : ∀ z ∈ Z, n z = z := fun z hz => hHZ _ hnH z hz
  refine ⟨fun z hz => ?_, fun φ hφZ hφH u hu => ?_, ?_, fun s hs u => ?_⟩
  · rw [mem_map_aut_iff, hZn z hz]
    exact hZU hz
  · rw [mem_map_aut_iff] at hu ⊢
    let ψ : W →* W := (n⁻¹ : MulAut W).toMonoidHom.comp (φ.comp n.toMonoidHom)
    have hψZ : ∀ z ∈ Z, ψ z ∈ Z := fun z hz => by
      change n⁻¹ (φ (n z)) ∈ Z
      rw [hZn' z hz, hZn _ (hφZ z hz)]
      exact hφZ z hz
    have hψH : ∀ h ∈ H, ∀ w : W, ψ (h w) * (h (ψ w))⁻¹ ∈ Z := by
      intro h hh w
      have hh' : n * h * n⁻¹ ∈ H := H.mul_mem (H.mul_mem hnH hh) hn'
      have h1 := hφH _ hh' (n w)
      have e1 : (n * h * n⁻¹) (n w) = n (h w) := by
        simp [MulAut.mul_apply]
      rw [e1] at h1
      have h2 := hZn _ h1
      change n⁻¹ (φ (n (h w))) * (h (n⁻¹ (φ (n w))))⁻¹ ∈ Z
      have e2 : h (n⁻¹ (φ (n w))) = n⁻¹ ((n * h * n⁻¹) (φ (n w))) := by
        simp [MulAut.mul_apply]
      rw [e2, ← map_inv, ← map_mul, h2]
      exact h1
    have := hEnd ψ hψZ hψH _ hu
    change n⁻¹ (φ (n (n⁻¹ u))) ∈ U at this
    simpa using this
  · have hZmap : Z.map n.toMonoidHom = Z := by
      ext z
      rw [mem_map_aut_iff]
      constructor
      · intro hz
        have h1 := hZn' _ hz
        rw [MulAut.apply_inv_self] at h1
        rw [h1]
        exact hz
      · intro hz
        rw [hZn z hz]
        exact hz
    rw [← hidx, ← Subgroup.relIndex_map_map_of_injective (f := n.toMonoidHom) Z U
      n.injective, hZmap]
  · have hnP' : n⁻¹ ∈ Subgroup.normalizer (P : Set (MulAut W)) := Subgroup.inv_mem _ hnP
    have ht : n⁻¹ * s * n ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp hnP' s).mp hs
      simpa using this
    rw [mem_map_aut_iff, mem_map_aut_iff]
    have e : n⁻¹ (s u) = (n⁻¹ * s * n) (n⁻¹ u) := by
      simp [MulAut.mul_apply]
    rw [e]
    exact hPU ht (n⁻¹ u)

theorem mem_stabW_of_unique (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (huniq : ∀ U', IsFlagW H P Z q i U' → U' = U) (hU : IsFlagW H P Z q i U) {n : MulAut W}
    (hnH : n ∈ H) (hnP : n ∈ Subgroup.normalizer (P : Set (MulAut W))) : n ∈ stabW U := by
  have hmap := huniq _ (isFlagW_map hHZ hnH hnP hU)
  rw [mem_stabW]
  intro u
  constructor
  · intro hu
    have : n u ∈ U.map n.toMonoidHom := ⟨u, hu, rfl⟩
    rwa [hmap] at this
  · intro hu
    rw [← hmap, mem_map_aut_iff] at hu
    simpa using hu

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
