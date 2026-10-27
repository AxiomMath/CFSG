module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MMembers
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16c2m_perm_zero : ∀ a : Fin 3, ∃ lam : Equiv.Perm (Fin 3), lam 0 = a := by
  decide

private theorem s16c2m_fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ n, P n := by
  intro n
  fin_cases n
  · exact h0
  · exact h1
  · exact h2

private theorem s16c2m_fix_of_endUnits {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {J : Subgroup W} (hE : Z391.EndUnitsTrivial L J) {τ : MulAut W}
    (hτ : ∀ l ∈ L, τ * l = l * τ) (hJ : J.map τ.toMonoidHom = J) : ∀ x ∈ J, τ x = x := by
  intro x hx
  let φ : ↥J ≃* ↥J := (MulEquiv.subgroupMap τ J).trans (MulEquiv.subgroupCongr hJ)
  have hφval : ∀ y : ↥J, ((φ y : ↥J) : W) = τ y := fun y => rfl
  have hφeqv : Z391.V2fEqv ↥L φ := by
    intro l y y' hyy
    show (l : MulAut W) ((φ y : ↥J) : W) = ((φ y' : ↥J) : W)
    rw [hφval y, hφval y']
    have h1 := congrArg (fun f : MulAut W => f y) (hτ l l.2)
    simp only [MulAut.mul_apply] at h1
    calc (l : MulAut W) (τ y) = τ ((l : MulAut W) y) := h1.symm
      _ = τ y' := by rw [show (l : MulAut W) y = y' from hyy]
  have hφ1 : φ = MulEquiv.refl _ := hE φ hφeqv
  have h2 : φ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    have := congrArg (fun ψ : ↥J ≃* ↥J => ψ ⟨x, hx⟩) hφ1
    simpa using this
  have h3 := congrArg (fun y : ↥J => (y : W)) h2
  rw [hφval ⟨x, hx⟩] at h3
  simpa using h3

private theorem s16c2m_eq_of_endUnits {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {J : Subgroup W} (hE : Z391.EndUnitsTrivial L J) {α β : MulAut W}
    (hα : ∀ l ∈ L, α * l = l * α) (hβ : ∀ l ∈ L, β * l = l * β)
    (hJ : J.map α.toMonoidHom = J.map β.toMonoidHom) : ∀ x ∈ J, α x = β x := by
  have hτ : ∀ l ∈ L, β⁻¹ * α * l = l * (β⁻¹ * α) := fun l hl =>
    Commute.mul_left (Commute.inv_left (show Commute β l from hβ l hl))
      (show Commute α l from hα l hl)
  have h1 : (J.map β.toMonoidHom).map β⁻¹.toMonoidHom = J := by
    rw [Subgroup.map_map]
    have : β⁻¹.toMonoidHom.comp β.toMonoidHom = MonoidHom.id W := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  have hmap : J.map (β⁻¹ * α).toMonoidHom = J := by
    have h2 : (β⁻¹ * α).toMonoidHom = β⁻¹.toMonoidHom.comp α.toMonoidHom := rfl
    rw [h2, ← Subgroup.map_map, hJ, h1]
  intro x hx
  have h3 : β⁻¹ (α x) = x := s16c2m_fix_of_endUnits hE hτ hmap x hx
  calc α x = β (β⁻¹ (α x)) := (MulAut.apply_inv_self W β _).symm
    _ = β x := by rw [h3]

private theorem s16c2m_members_zero {W : Type} [CommGroup W] [Finite W]
    {X L K : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁)
    (hKX : K ≤ X) (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) (hK : IsSym ↥K 3)
    (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁) :
    ∃ (G3 : Fin 3 → Subgroup W) (π : ↥X →* Equiv.Perm (Fin 3)), G3 0 = J₀ ∧
      (∀ (x : ↥X) (i : Fin 3), (G3 i).map (x : MulAut W).toMonoidHom = G3 (π x i)) ∧
      (∀ σ : Equiv.Perm (Fin 3), ∃ k : ↥K, π ⟨(k : MulAut W), hKX k.2⟩ = σ) ∧
      (∀ k : ↥K, π ⟨(k : MulAut W), hKX k.2⟩ = 1 → k = 1) ∧
      (∀ i j : Fin 3, i ≠ j → G3 i ⊓ G3 j = ⊥ ∧ G3 i ⊔ G3 j = ⊤) ∧
      (∀ g : ↥X, (∀ k ∈ K, (g : MulAut W) * k = k * (g : MulAut W)) → π g = 1) := by
  obtain ⟨G3, π, -, -, ⟨a, ha⟩, -, hact, hsurj, hfaith, hmeet, -, hcomm⟩ :=
    s16c2m_members F hKX hKL hK hE₀ hE₁
  obtain ⟨lam, hlam⟩ := s16c2m_perm_zero a
  let π' : ↥X →* Equiv.Perm (Fin 3) :=
    { toFun := fun x => lam⁻¹ * π x * lam
      map_one' := by simp
      map_mul' := fun x y => by simp [mul_assoc] }
  refine ⟨fun i => G3 (lam i), π', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show G3 (lam 0) = J₀
    rw [hlam]
    exact ha
  · intro x i
    show (G3 (lam i)).map (x : MulAut W).toMonoidHom = G3 (lam ((lam⁻¹ * π x * lam) i))
    have : lam ((lam⁻¹ * π x * lam) i) = π x (lam i) := by simp [Equiv.Perm.mul_apply]
    rw [hact x (lam i), this]
  · intro σ
    obtain ⟨k, hk⟩ := hsurj (lam * σ * lam⁻¹)
    refine ⟨k, ?_⟩
    show lam⁻¹ * π ⟨(k : MulAut W), hKX k.2⟩ * lam = σ
    rw [hk]
    group
  · intro k hk
    apply hfaith k
    have h : lam⁻¹ * π ⟨(k : MulAut W), hKX k.2⟩ * lam = 1 := hk
    calc π ⟨(k : MulAut W), hKX k.2⟩
        = lam * (lam⁻¹ * π ⟨(k : MulAut W), hKX k.2⟩ * lam) * lam⁻¹ := by group
      _ = 1 := by rw [h]; group
  · intro i j hij
    exact hmeet (lam i) (lam j) (fun h => hij (lam.injective h))
  · intro g hg
    show lam⁻¹ * π g * lam = 1
    rw [hcomm g hg]
    group

private theorem s16c2m_model_core {W : Type} [CommGroup W] (hW : ∀ w : W, w ^ 2 = 1)
    {L K : Subgroup (MulAut W)} {J : Subgroup W} (G3 : Fin 3 → Subgroup W) (hG0 : G3 0 = J)
    (s : ↥K ≃* Equiv.Perm (Fin 3))
    (hs : ∀ (κ : ↥K) (i : Fin 3), (G3 i).map (κ : MulAut W).toMonoidHom = G3 (s κ i))
    (hmeet : ∀ i j : Fin 3, i ≠ j → G3 i ⊓ G3 j = ⊥ ∧ G3 i ⊔ G3 j = ⊤)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) (hE : Z391.EndUnitsTrivial L J) :
    ∃ ψ : W ≃* ↥(s16c2m_Triples ↥J),
      (∀ x : ↥J, (ψ (x : W)).1 = ![1, x, x]) ∧
      (∀ w : W, w ∈ J ↔ (ψ w).1 0 = 1) ∧
      (∀ (κ : ↥K) (w : W) (i : Fin 3), (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i)) ∧
      (∀ g : MulAut W, (∀ k ∈ K, g * k = k * g) → J.map g.toMonoidHom = J →
        ∀ (w : W) (i : Fin 3), (((ψ (g w)).1 i : ↥J) : W) = g (((ψ w).1 i : ↥J) : W)) := by
  classical
  have hsq : ∀ w : W, w * w = 1 := fun w => by simpa [sq] using hW w
  have hu2 : ∀ u : ↥J, u * u = 1 := fun u => Subtype.ext (hsq u)
  obtain ⟨r, hr0, hr1, hr2, hr3⟩ : ∃ r : Equiv.Perm (Fin 3),
      r 0 = 1 ∧ r 1 = 2 ∧ r 2 = 0 ∧ r ^ 3 = 1 :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide, by decide, by decide⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ↥K, s ζ = r := ⟨s.symm r, s.apply_symm_apply r⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : ↥K, s τ = Equiv.swap 0 1 := ⟨s.symm _, s.apply_symm_apply _⟩
  obtain ⟨ζ', hζ'K, hζ'⟩ : ∃ (ζ' : MulAut W) (h : ζ' ∈ K), s ⟨ζ', h⟩ = r := ⟨ζ, ζ.2, hζ⟩
  have hζmap : ∀ i, (G3 i).map ζ'.toMonoidHom = G3 (r i) := by
    intro i
    have h := hs ⟨ζ', hζ'K⟩ i
    rw [hζ'] at h
    exact h
  have hζ3 : ζ' * ζ' * ζ' = 1 := by
    have h : (⟨ζ', hζ'K⟩ : ↥K) ^ 3 = 1 := by
      apply s.injective
      rw [map_pow, hζ', hr3, map_one]
    have := congrArg (fun k : ↥K => (k : MulAut W)) h
    simpa [pow_succ] using this
  have hζ3' : ∀ x : W, ζ' (ζ' (ζ' x)) = x := fun x => by
    have := congrArg (fun f : MulAut W => f x) hζ3
    simpa [MulAut.mul_apply] using this
  obtain ⟨z, hz0, hz1, hz2⟩ : ∃ z : Fin 3 → MulAut W, z 0 = 1 ∧ z 1 = ζ' ∧ z 2 = ζ' * ζ' :=
    ⟨![1, ζ', ζ' * ζ'], rfl, rfl, rfl⟩
  have hz0' : ∀ u : W, z 0 u = u := fun u => by rw [hz0]; rfl
  have hz1' : ∀ u : W, z 1 u = ζ' u := fun u => by rw [hz1]
  have hz2' : ∀ u : W, z 2 u = ζ' (ζ' u) := fun u => by rw [hz2]; rfl
  have hid : (1 : MulAut W).toMonoidHom = MonoidHom.id W := by
    ext x
    rfl
  have hzmap : ∀ n, (G3 0).map (z n).toMonoidHom = G3 n := by
    refine s16c2m_fin3_cases ?_ ?_ ?_
    · rw [hz0, hid, Subgroup.map_id]
    · rw [hz1, hζmap 0, hr0]
    · have h : (ζ' * ζ').toMonoidHom = ζ'.toMonoidHom.comp ζ'.toMonoidHom := rfl
      rw [hz2, h, ← Subgroup.map_map, hζmap 0, hr0, hζmap 1, hr1]
  have hzcomm : ∀ n, ∀ l ∈ L, z n * l = l * z n := by
    refine s16c2m_fin3_cases ?_ ?_ ?_
    · intro l _
      rw [hz0, one_mul, mul_one]
    · intro l hl
      rw [hz1]
      exact hKL ζ' hζ'K l hl
    · intro l hl
      rw [hz2]
      exact Commute.mul_left (show Commute ζ' l from hKL ζ' hζ'K l hl)
        (show Commute ζ' l from hKL ζ' hζ'K l hl)
  have hstar : ∀ (κ : ↥K) (n : Fin 3), ∀ u ∈ J, (κ : MulAut W) (z n u) = z (s κ n) u := by
    intro κ n u hu
    have hκc : ∀ l ∈ L, (κ : MulAut W) * l = l * (κ : MulAut W) := hKL κ κ.2
    have hα : ∀ l ∈ L, (κ : MulAut W) * z n * l = l * ((κ : MulAut W) * z n) := fun l hl =>
      Commute.mul_left (show Commute (κ : MulAut W) l from hκc l hl)
        (show Commute (z n) l from hzcomm n l hl)
    have hmap : J.map ((κ : MulAut W) * z n).toMonoidHom = J.map (z (s κ n)).toMonoidHom := by
      have h1 : ((κ : MulAut W) * z n).toMonoidHom =
          (κ : MulAut W).toMonoidHom.comp (z n).toMonoidHom := rfl
      rw [← hG0, h1, ← Subgroup.map_map, hzmap n, hs κ n, hzmap (s κ n)]
    have := s16c2m_eq_of_endUnits hE hα (hzcomm (s κ n)) hmap u hu
    simpa [MulAut.mul_apply] using this
  have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have e1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have hτ1 : ∀ u ∈ J, (τ : MulAut W) u = ζ' u := by
    intro u hu
    have h := hstar τ 0 u hu
    rw [hz0' u, hτ, e0, hz1' u] at h
    exact h
  have hτ2 : ∀ u ∈ J, (τ : MulAut W) (ζ' u) = u := by
    intro u hu
    have h := hstar τ 1 u hu
    rw [hz1' u, hτ, e1, hz0' u] at h
    exact h
  have hτ3 : ∀ u ∈ J, (τ : MulAut W) (ζ' (ζ' u)) = ζ' (ζ' u) := by
    intro u hu
    have h := hstar τ 2 u hu
    rw [hz2' u, hτ, e2, hz2' u] at h
    exact h
  have hJmap : J.map ζ'.toMonoidHom = G3 1 := by
    rw [← hG0, hζmap 0, hr0]
  have hd : Disjoint J (J.map ζ'.toMonoidHom) := by
    rw [hJmap, ← hG0]
    exact disjoint_iff.2 (hmeet 0 1 (by decide)).1
  have hsup : J ⊔ J.map ζ'.toMonoidHom = ⊤ := by
    rw [hJmap, ← hG0]
    exact (hmeet 0 1 (by decide)).2
  have hex : ∀ y ∈ J, ∃ v : ↥J, ζ' (ζ' y) = (v : W) * ζ' (v : W) := by
    intro y hy
    obtain ⟨a', b', hab⟩ := s16c2m_exists_pair hsup (ζ' (ζ' y))
    have h1 : (τ : MulAut W) (ζ' (ζ' y)) = ζ' (ζ' y) := hτ3 y hy
    have h2 : (τ : MulAut W) (ζ' (ζ' y)) = ζ' (a' : W) * (b' : W) := by
      rw [hab, map_mul, hτ1 a' a'.2, hτ2 b' b'.2]
    have h4 : (a' : W) * ζ' (b' : W) = ζ' (a' : W) * (b' : W) := by
      rw [← hab, ← h1, h2]
    have h3 : (a' : W) * (b' : W) = ζ' ((a' : W) * (b' : W)) := by
      calc (a' : W) * (b' : W) = ((a' : W) * ζ' (b' : W)) * ((b' : W) * ζ' (b' : W)) := by
            rw [mul_mul_mul_comm, hsq (ζ' (b' : W)), mul_one]
        _ = (ζ' (a' : W) * (b' : W)) * ((b' : W) * ζ' (b' : W)) := by rw [h4]
        _ = (ζ' (a' : W) * ζ' (b' : W)) * ((b' : W) * (b' : W)) := by
            simp only [mul_assoc, mul_comm, mul_left_comm]
        _ = ζ' ((a' : W) * (b' : W)) := by rw [hsq (b' : W), mul_one, map_mul]
    have h5 : (a' : W) * (b' : W) ∈ J ⊓ J.map ζ'.toMonoidHom :=
      ⟨J.mul_mem a'.2 b'.2, ⟨(a' : W) * (b' : W), J.mul_mem a'.2 b'.2, h3.symm⟩⟩
    rw [disjoint_iff.1 hd, Subgroup.mem_bot] at h5
    have h6 : (a' : W) = (b' : W) := by
      have := congrArg (fun x : W => x * (b' : W)) h5
      simpa [mul_assoc, hsq] using this
    exact ⟨a', by rw [hab, h6]⟩
  have hR : ∀ x ∈ J, ζ' (ζ' x) = x * ζ' x := by
    intro x hx
    obtain ⟨v, hv⟩ := hex x hx
    obtain ⟨v₂, hv₂⟩ := hex (v : W) v.2
    have h1 : x = (v₂ : W) * ζ' ((v : W) * (v₂ : W)) := by
      calc x = ζ' (ζ' (ζ' x)) := (hζ3' x).symm
        _ = ζ' ((v : W) * ζ' (v : W)) := by rw [hv]
        _ = ζ' (v : W) * ζ' (ζ' (v : W)) := by rw [map_mul]
        _ = ζ' (v : W) * ((v₂ : W) * ζ' (v₂ : W)) := by rw [hv₂]
        _ = (v₂ : W) * ζ' ((v : W) * (v₂ : W)) := by
            rw [map_mul]
            simp only [mul_assoc, mul_comm, mul_left_comm]
    have h2 : (⟨x, hx⟩ : ↥J) = v₂ ∧ (1 : ↥J) = v * v₂ := by
      apply s16c2m_pair_unique hd
      show x * ζ' ((1 : ↥J) : W) = (v₂ : W) * ζ' ((v : W) * (v₂ : W))
      rw [← h1]
      simp
    have hvx : (v : W) = x := by
      have h7 : (v : W) * (v₂ : W) = 1 := (congrArg Subtype.val h2.2).symm
      have h8 : (v₂ : W) = x := (congrArg Subtype.val h2.1).symm
      rw [h8] at h7
      calc (v : W) = (v : W) * (x * x) := by rw [hsq x, mul_one]
        _ = ((v : W) * x) * x := by rw [mul_assoc]
        _ = x := by rw [h7, one_mul]
    rw [hv, hvx]
  obtain ⟨ψ, hψ⟩ := s16c2m_pair_model hW hd hsup
  have hψz : ∀ (p : Fin 3) (u : ↥J) (j : Fin 3),
      (ψ (z p (u : W))).1 j = if j = p then 1 else u := by
    intro p u j
    refine s16c2m_fin3_cases
      (P := fun p => (ψ (z p (u : W))).1 j = if j = p then 1 else u) ?_ ?_ ?_ p
    · have e : z 0 (u : W) = (u : W) * ζ' ((1 : ↥J) : W) := by
        rw [hz0' u]
        simp
      show (ψ (z 0 (u : W))).1 j = if j = 0 then 1 else u
      rw [e, hψ u 1 j]
      fin_cases j <;> simp
    · have e : z 1 (u : W) = ((1 : ↥J) : W) * ζ' (u : W) := by
        rw [hz1' u]
        simp
      show (ψ (z 1 (u : W))).1 j = if j = 1 then 1 else u
      rw [e, hψ 1 u j]
      fin_cases j <;> simp
    · have e : z 2 (u : W) = (u : W) * ζ' (u : W) := by rw [hz2' u, hR u u.2]
      show (ψ (z 2 (u : W))).1 j = if j = 2 then 1 else u
      rw [e, hψ u u j]
      fin_cases j <;> simp [hu2]
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro x
    funext j
    have e : (x : W) = (x : W) * ζ' ((1 : ↥J) : W) := by simp
    rw [e, hψ x 1 j]
    fin_cases j <;> simp
  · intro w
    constructor
    · intro hw
      have e : w = ((⟨w, hw⟩ : ↥J) : W) * ζ' ((1 : ↥J) : W) := by simp
      rw [e, hψ ⟨w, hw⟩ 1 0]
      simp
    · intro h0
      obtain ⟨u, v, rfl⟩ := s16c2m_exists_pair hsup w
      rw [hψ u v 0] at h0
      have hv : v = 1 := by simpa using h0
      rw [hv]
      simp
  · intro κ w i
    obtain ⟨u, v, rfl⟩ := s16c2m_exists_pair hsup w
    have hκu : (κ : MulAut W) (u : W) = z (s κ 0) (u : W) := by
      have := hstar κ 0 u u.2
      rwa [hz0' u] at this
    have hκv : (κ : MulAut W) (ζ' (v : W)) = z (s κ 1) (v : W) := by
      have := hstar κ 1 v v.2
      rwa [hz1' v] at this
    rw [map_mul, hκu, hκv, map_mul, Subgroup.coe_mul, Pi.mul_apply, hψz, hψz, hψ]
    simp only [Equiv.Perm.inv_eq_iff_eq]
  · intro g hg hgJ w i
    obtain ⟨u, v, rfl⟩ := s16c2m_exists_pair hsup w
    have hgu : g (u : W) ∈ J := by
      have h := Subgroup.mem_map_of_mem g.toMonoidHom u.2
      rw [hgJ] at h
      exact h
    have hgv : g (v : W) ∈ J := by
      have h := Subgroup.mem_map_of_mem g.toMonoidHom v.2
      rw [hgJ] at h
      exact h
    have hgζ : g (ζ' (v : W)) = ζ' (g (v : W)) := by
      have := congrArg (fun f : MulAut W => f (v : W)) (hg ζ' hζ'K)
      simpa [MulAut.mul_apply] using this
    have e : g ((u : W) * ζ' (v : W)) =
        ((⟨g u, hgu⟩ : ↥J) : W) * ζ' ((⟨g v, hgv⟩ : ↥J) : W) := by
      rw [map_mul, hgζ]
    rw [e, hψ ⟨g u, hgu⟩ ⟨g v, hgv⟩ i, hψ u v i]
    fin_cases i <;> simp

theorem s16c2m_model {W : Type} [CommGroup W] [Finite W] {X L K : Subgroup (MulAut W)}
    {J₀ J₁ : Subgroup W} (F : Cfg2Setting X L J₀ J₁) (hKX : K ≤ X)
    (hKL : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k) (hK : IsSym ↥K 3)
    (hE₀ : Z391.EndUnitsTrivial L J₀) (hE₁ : Z391.EndUnitsTrivial L J₁) :
    ∃ (s : ↥K ≃* Equiv.Perm (Fin 3)) (ψ : W ≃* ↥(s16c2m_Triples ↥J₀)),
      (∀ x : ↥J₀, (ψ (x : W)).1 = ![1, x, x]) ∧
      (∀ w : W, w ∈ J₀ ↔ (ψ w).1 0 = 1) ∧
      (∀ (κ : ↥K) (w : W) (i : Fin 3), (ψ ((κ : MulAut W) w)).1 i = (ψ w).1 ((s κ)⁻¹ i)) ∧
      (∀ g ∈ X, (∀ k ∈ K, g * k = k * g) → ∀ (w : W) (i : Fin 3),
        (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W)) := by
  obtain ⟨G3, π, hG0, hact, hsurj, hfaith, hmeet, hcomm⟩ :=
    s16c2m_members_zero F hKX hKL hK hE₀ hE₁
  let πK : ↥K →* Equiv.Perm (Fin 3) := π.comp (Subgroup.inclusion hKX)
  have hinj : Function.Injective πK := by
    rw [injective_iff_map_eq_one]
    intro k hk
    exact hfaith k hk
  have hbij : Function.Bijective πK := by
    refine ⟨hinj, fun σ => ?_⟩
    obtain ⟨k, hk⟩ := hsurj σ
    exact ⟨k, hk⟩
  let s : ↥K ≃* Equiv.Perm (Fin 3) := MulEquiv.ofBijective πK hbij
  have hs : ∀ (κ : ↥K) (i : Fin 3),
      (G3 i).map (κ : MulAut W).toMonoidHom = G3 (s κ i) := fun κ i =>
    hact ⟨(κ : MulAut W), hKX κ.2⟩ i
  obtain ⟨ψ, h1, h2, h3, h4⟩ := s16c2m_model_core F.sq G3 hG0 s hs hmeet hKL hE₀
  refine ⟨s, ψ, h1, h2, h3, ?_⟩
  intro g hgX hgK w i
  have hπ : π ⟨g, hgX⟩ = 1 := hcomm ⟨g, hgX⟩ hgK
  have hgJ : J₀.map g.toMonoidHom = J₀ := by
    have h := hact ⟨g, hgX⟩ 0
    rw [hπ, Equiv.Perm.one_apply, hG0] at h
    exact h
  exact h4 g hgK hgJ w i

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
