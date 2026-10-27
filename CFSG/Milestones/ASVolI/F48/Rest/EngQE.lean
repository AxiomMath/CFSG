module

public import CFSG.Milestones.ASVolI.F48.Rest.Eng

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.CosetTable
open CFSG.Open CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

variable {D : Type} [Group D] {P1 P2 : Subgroup D} {m : ℕ}

theorem burnsideF48t_qe_of_core {Q : Subgroup D → Prop} (hcore : burnsideF48t_ECore P1 P2 m Q)
    {E : Type} [Group E] [Finite E] {M₁ M₂ : Subgroup E} (θ : D ≃* E)
    {A₁ A₂ : Subgroup D} (hA : (A₁ = P1 ∧ A₂ = P2) ∨ (A₁ = P2 ∧ A₂ = P1))
    (hM1 : M₁ = A₁.map θ.toMonoidHom) (hM2 : M₂ = A₂.map θ.toMonoidHom) (hgen : M₁ ⊔ M₂ = ⊤)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hcard : Nat.card D ≤ Nat.card Y)
    {a : ↥M₁} {b : ↥M₂} {K' : Subgroup E} (haM : (a : E) ∉ M₂) (hbM : (b : E) ∉ M₁)
    (hK'le : K' ≤ M₁ ⊓ M₂) (hQ : Q (K'.comap θ.toMonoidHom))
    (haK : ∀ k ∈ K', (a : E) * k * (a : E)⁻¹ ∈ K') (hbK : ∀ k ∈ K', (b : E) * k * (b : E)⁻¹ ∈ K')
    (ha2 : (a : E) * a ∈ K') (hb2 : (b : E) * b ∈ K')
    (hrel : ∀ (a' : ↥M₁) (b' : ↥M₂), (a : E)⁻¹ * a' ∈ K' → (b : E)⁻¹ * b' ∈ K' →
      ∃ c : ↥(M₁ ⊓ M₂), (c : E) ∈ K' ∧ (β.φ1 a' * β.φ2 b') ^ m = β.φ12 c) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion := by
  let eG : ↥(M₁ ⊔ M₂) ≃* E := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have h12β : ∀ (t : E) (h1 : t ∈ M₁) (h2 : t ∈ M₂), β.φ1 ⟨t, h1⟩ = β.φ2 ⟨t, h2⟩ :=
    fun t h1 h2 => (β.comm1 ⟨t, ⟨h1, h2⟩⟩).trans (β.comm2 ⟨t, ⟨h1, h2⟩⟩).symm
  have hmemθ : ∀ {A : Subgroup D} {M : Subgroup E}, M = A.map θ.toMonoidHom →
      ∀ z, θ z ∈ M ↔ z ∈ A := by
    intro A M hM z
    rw [hM]
    exact Subgroup.mem_map_iff_mem θ.injective
  have hpre : ∀ {A : Subgroup D} {M : Subgroup E}, M = A.map θ.toMonoidHom →
      ∀ u : ↥M, ∃ z, z ∈ A ∧ θ z = u := by
    intro A M hM u
    obtain ⟨z, hz, hzu⟩ : (u : E) ∈ A.map θ.toMonoidHom := by rw [← hM]; exact u.2
    exact ⟨z, hz, hzu⟩
  set K'' : Subgroup D := K'.comap θ.toMonoidHom with hK''
  have hθK : ∀ z, z ∈ K'' ↔ θ z ∈ K' := fun z => Iff.rfl
  have hB : ∀ z, θ z ∈ M₁ ⊓ M₂ ↔ z ∈ P1 ⊓ P2 := by
    intro z
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hmemθ hM1, hmemθ hM2]
    rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Iff.rfl
    · exact and_comm
  have hK''le : K'' ≤ P1 ⊓ P2 := fun z hz => (hB z).1 (hK'le ((hθK z).1 hz))
  have hconjE : ∀ {z : E}, (∀ k ∈ K', z * k * z⁻¹ ∈ K') → ∀ z₀ : D, θ z₀ = z →
      ∀ k ∈ K'', z₀ * k * z₀⁻¹ ∈ K'' := by
    intro z hz z₀ hz₀ k hk
    rw [hθK, map_mul, map_mul, map_inv, hz₀]
    exact hz _ ((hθK k).1 hk)
  have hsqE : ∀ {z : E}, z * z ∈ K' → ∀ z₀ : D, θ z₀ = z → z₀ * z₀ ∈ K'' := by
    intro z hz z₀ hz₀
    rw [hθK, map_mul, hz₀]
    exact hz
  rcases hA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩
  · rw [hA1] at hM1
    rw [hA2] at hM2
    let r₁ : ↥P1 ≃* ↥M₁ := (θ.subgroupMap P1).trans (MulEquiv.subgroupCongr hM1.symm)
    let r₂ : ↥P2 ≃* ↥M₂ := (θ.subgroupMap P2).trans (MulEquiv.subgroupCongr hM2.symm)
    have hr₁ : ∀ z : ↥P1, ((r₁ z : ↥M₁) : E) = θ z := fun z => rfl
    have hr₂ : ∀ z : ↥P2, ((r₂ z : ↥M₂) : E) = θ z := fun z => rfl
    let f₁ : ↥P1 →* Y := β.φ1.comp r₁.toMonoidHom
    let f₂ : ↥P2 →* Y := β.φ2.comp r₂.toMonoidHom
    have hf12 : ∀ (t : D) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩ := fun t h =>
      h12β (θ t) _ _
    have hfgen : f₁.range ⊔ f₂.range = ⊤ := by
      rw [show f₁.range = β.φ1.range from burnsideF48s_e_range_comp _ _,
        show f₂.range = β.φ2.range from burnsideF48s_e_range_comp _ _]
      exact β.gen
    have hfinj : Function.Injective f₁ := hβ.1.comp r₁.injective
    obtain ⟨x, hx, hxa⟩ := hpre hM1 a
    obtain ⟨y, hy, hyb⟩ := hpre hM2 b
    have hx2 : x ∉ P2 := fun h => haM (hxa ▸ (hmemθ hM2 x).2 h)
    have hy1 : y ∉ P1 := fun h => hbM (hyb ▸ (hmemθ hM1 y).2 h)
    have hrel' : ∀ k₁ (hk₁ : k₁ ∈ K'') k₂ (hk₂ : k₂ ∈ K''), ∃ c, ∃ hc : c ∈ K'',
        (f₁ ⟨x * k₁, P1.mul_mem hx (hK''le hk₁).1⟩ *
          f₂ ⟨y * k₂, P2.mul_mem hy (hK''le hk₂).2⟩) ^ m = f₁ ⟨c, (hK''le hc).1⟩ := by
      intro k₁ hk₁ k₂ hk₂
      have ha' : (a : E)⁻¹ * (r₁ ⟨x * k₁, P1.mul_mem hx (hK''le hk₁).1⟩ : ↥M₁) ∈ K' := by
        rw [hr₁]
        show (a : E)⁻¹ * θ (x * k₁) ∈ K'
        rw [map_mul, hxa, inv_mul_cancel_left]
        exact hk₁
      have hb' : (b : E)⁻¹ * (r₂ ⟨y * k₂, P2.mul_mem hy (hK''le hk₂).2⟩ : ↥M₂) ∈ K' := by
        rw [hr₂]
        show (b : E)⁻¹ * θ (y * k₂) ∈ K'
        rw [map_mul, hyb, inv_mul_cancel_left]
        exact hk₂
      obtain ⟨c, hcK, hrc⟩ := hrel _ _ ha' hb'
      obtain ⟨c₀, hc₀, hc₀c⟩ := hpre (A := P1) hM1 ⟨c, c.2.1⟩
      have hc₀K : c₀ ∈ K'' := by rw [hθK, hc₀c]; exact hcK
      refine ⟨c₀, hc₀K, ?_⟩
      have hrc₀ : r₁ ⟨c₀, (hK''le hc₀K).1⟩ = ⟨c, c.2.1⟩ := Subtype.ext hc₀c
      show (β.φ1 (r₁ _) * β.φ2 (r₂ _)) ^ m = β.φ1 (r₁ ⟨c₀, (hK''le hc₀K).1⟩)
      rw [hrc, hrc₀]
      exact (β.comm1 c).symm
    obtain ⟨φ, hφ1, hφ2⟩ := hcore Y f₁ f₂ hf12 hfgen hfinj hcard K'' hK''le hQ x y hx hy hx2
      (hconjE haK x hxa) (hsqE ha2 x hxa) hy1 (hconjE hbK y hyb) (hsqE hb2 y hyb) hrel'
    refine burnsideF48s_qe_of_equiv β hβ (φ.trans (θ.trans eG.symm)) (fun u => ?_) (fun u => ?_)
    · obtain ⟨z, hz, hzu⟩ := hpre hM1 u
      have hu : u = r₁ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₁ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ1]
      exact (hmemθ hM1 z).2 hz
    · obtain ⟨z, hz, hzu⟩ := hpre hM2 u
      have hu : u = r₂ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₂ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ2]
      exact (hmemθ hM2 z).2 hz
  · rw [hA1] at hM1
    rw [hA2] at hM2
    let r₁ : ↥P1 ≃* ↥M₂ := (θ.subgroupMap P1).trans (MulEquiv.subgroupCongr hM2.symm)
    let r₂ : ↥P2 ≃* ↥M₁ := (θ.subgroupMap P2).trans (MulEquiv.subgroupCongr hM1.symm)
    have hr₁ : ∀ z : ↥P1, ((r₁ z : ↥M₂) : E) = θ z := fun z => rfl
    have hr₂ : ∀ z : ↥P2, ((r₂ z : ↥M₁) : E) = θ z := fun z => rfl
    let f₁ : ↥P1 →* Y := β.φ2.comp r₁.toMonoidHom
    let f₂ : ↥P2 →* Y := β.φ1.comp r₂.toMonoidHom
    have hf12 : ∀ (t : D) (h : t ∈ P1 ⊓ P2), f₁ ⟨t, h.1⟩ = f₂ ⟨t, h.2⟩ := fun t h =>
      (h12β (θ t) _ _).symm
    have hfgen : f₁.range ⊔ f₂.range = ⊤ := by
      rw [show f₁.range = β.φ2.range from burnsideF48s_e_range_comp _ _,
        show f₂.range = β.φ1.range from burnsideF48s_e_range_comp _ _, sup_comm]
      exact β.gen
    have hfinj : Function.Injective f₁ := hβ.2.2.comp r₁.injective
    have haK' := burnsideF48s_e_conj_inv_mem haK
    obtain ⟨x, hx, hxb⟩ := hpre hM2 b
    obtain ⟨y, hy, hya⟩ := hpre hM1 a
    have hx2 : x ∉ P2 := fun h => hbM (hxb ▸ (hmemθ hM1 x).2 h)
    have hy1 : y ∉ P1 := fun h => haM (hya ▸ (hmemθ hM2 y).2 h)
    have hrel' : ∀ k₁ (hk₁ : k₁ ∈ K'') k₂ (hk₂ : k₂ ∈ K''), ∃ c, ∃ hc : c ∈ K'',
        (f₁ ⟨x * k₁, P1.mul_mem hx (hK''le hk₁).1⟩ *
          f₂ ⟨y * k₂, P2.mul_mem hy (hK''le hk₂).2⟩) ^ m = f₁ ⟨c, (hK''le hc).1⟩ := by
      intro k₁ hk₁ k₂ hk₂
      set b' : ↥M₂ := r₁ ⟨x * k₁, P1.mul_mem hx (hK''le hk₁).1⟩ with hb'def
      set a' : ↥M₁ := r₂ ⟨y * k₂, P2.mul_mem hy (hK''le hk₂).2⟩ with ha'def
      have hb'E : (b' : E) = b * θ k₁ := by rw [hb'def, hr₁, map_mul, hxb]
      have ha'E : (a' : E) = a * θ k₂ := by rw [ha'def, hr₂, map_mul, hya]
      have ha' : (a : E)⁻¹ * a' ∈ K' := by rw [ha'E, inv_mul_cancel_left]; exact hk₂
      have hb' : (b : E)⁻¹ * b' ∈ K' := by rw [hb'E, inv_mul_cancel_left]; exact hk₁
      obtain ⟨c, hcK, hrc⟩ := hrel a' b' ha' hb'
      have hdK : (a' : E)⁻¹ * c * a' ∈ K' := by
        rw [ha'E]
        have e : (a * θ k₂ : E)⁻¹ * c * (a * θ k₂) = (θ k₂)⁻¹ * ((a : E)⁻¹ * c * a) * θ k₂ := by
          group
        rw [e]
        exact K'.mul_mem (K'.mul_mem (K'.inv_mem hk₂) (haK' _ hcK)) hk₂
      have hdM := hK'le hdK
      obtain ⟨d₀, hd₀, hd₀d⟩ := hpre (A := P1) hM2 ⟨_, hdM.2⟩
      have hd₀K : d₀ ∈ K'' := by rw [hθK, hd₀d]; exact hdK
      refine ⟨d₀, hd₀K, ?_⟩
      have hrd : r₁ ⟨d₀, (hK''le hd₀K).1⟩ = ⟨_, hdM.2⟩ := Subtype.ext hd₀d
      show (β.φ2 b' * β.φ1 a') ^ m = β.φ2 (r₁ ⟨d₀, (hK''le hd₀K).1⟩)
      rw [hrd, ← h12β _ hdM.1 hdM.2]
      have e1 : (⟨(a' : E)⁻¹ * c * a', hdM.1⟩ : ↥M₁) = a'⁻¹ * ⟨c, c.2.1⟩ * a' := rfl
      have e2 : (β.φ2 b' * β.φ1 a') ^ m = (β.φ1 a')⁻¹ * (β.φ1 a' * β.φ2 b') ^ m * β.φ1 a' := by
        rw [show (β.φ1 a')⁻¹ * (β.φ1 a' * β.φ2 b') ^ m * β.φ1 a' =
            ((β.φ1 a')⁻¹ * (β.φ1 a' * β.φ2 b') * ((β.φ1 a')⁻¹)⁻¹) ^ m by rw [conj_pow, inv_inv]]
        congr 1
        group
      have e3 : ∀ u v w : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1,
          β.φ1 (u⁻¹ * v * w) = (β.φ1 u)⁻¹ * β.φ1 v * β.φ1 w := by
        intro u v w
        rw [map_mul, map_mul, map_inv]
      rw [e2, hrc]
      have e5 : β.φ1 ⟨(a' : E)⁻¹ * c * a', hdM.1⟩ = (β.φ1 a')⁻¹ * β.φ1 ⟨c, c.2.1⟩ * β.φ1 a' :=
        (congrArg β.φ1 e1).trans (e3 a' ⟨c, c.2.1⟩ a')
      rw [e5]
      exact congrArg (fun z => (β.φ1 a')⁻¹ * z * β.φ1 a') (β.comm1 c).symm
    obtain ⟨φ, hφ1, hφ2⟩ := hcore Y f₁ f₂ hf12 hfgen hfinj hcard K'' hK''le hQ x y hx hy hx2
      (hconjE hbK x hxb) (hsqE hb2 x hxb) hy1 (hconjE haK y hya) (hsqE ha2 y hya) hrel'
    refine burnsideF48s_qe_of_equiv β hβ (φ.trans (θ.trans eG.symm)) (fun u => ?_) (fun u => ?_)
    · obtain ⟨z, hz, hzu⟩ := hpre hM1 u
      have hu : u = r₂ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₂ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ2]
      exact (hmemθ hM1 z).2 hz
    · obtain ⟨z, hz, hzu⟩ := hpre hM2 u
      have hu : u = r₁ ⟨z, hz⟩ := Subtype.ext hzu.symm
      rw [hu]
      show ((eG.symm (θ (φ (f₁ ⟨z, hz⟩))) : ↥(M₁ ⊔ M₂)) : E) ∈ _
      rw [hφ1]
      exact (hmemθ hM2 z).2 hz

variable {n : ℕ} {G : Fin n → D} {S1 S2 : Set (Fin n)} {K : Subgroup D}
  {R1 R2 XW YW KW : List (List (Fin n × Bool))}

theorem burnsideF48t_qe [Finite D] (hF : burnsideF48t_Facts G P1 P2 S1 S2 K R1 R2 XW YW KW m)
    (hconj : ∀ K'' : Subgroup D, K'' ≤ P1 ⊓ P2 → Nat.card ↥K'' = Nat.card ↥K →
      ∃ t ∈ P1 ⊓ P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ K)
    {E : Type} [Group E] [Finite E] {M₁ M₂ : Subgroup E} (θ : D ≃* E)
    {A₁ A₂ : Subgroup D} (hA : (A₁ = P1 ∧ A₂ = P2) ∨ (A₁ = P2 ∧ A₂ = P1))
    (hM1 : M₁ = A₁.map θ.toMonoidHom) (hM2 : M₂ = A₂.map θ.toMonoidHom) (hgen : M₁ ⊔ M₂ = ⊤)
    {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hcard : Nat.card D ≤ Nat.card Y)
    {a : ↥M₁} {b : ↥M₂} {K' : Subgroup E} (haM : (a : E) ∉ M₂) (hbM : (b : E) ∉ M₁)
    (hK'le : K' ≤ M₁ ⊓ M₂) (hK'card : Nat.card ↥K' = Nat.card ↥K)
    (haK : ∀ k ∈ K', (a : E) * k * (a : E)⁻¹ ∈ K') (hbK : ∀ k ∈ K', (b : E) * k * (b : E)⁻¹ ∈ K')
    (ha2 : (a : E) * a ∈ K') (hb2 : (b : E) * b ∈ K')
    (hrel : ∀ (a' : ↥M₁) (b' : ↥M₂), (a : E)⁻¹ * a' ∈ K' → (b : E)⁻¹ * b' ∈ K' →
      ∃ c : ↥(M₁ ⊓ M₂), (c : E) ∈ K' ∧ (β.φ1 a' * β.φ2 b') ^ m = β.φ12 c) :
    Amalgam.Completion.IsQuasiEquivalent β.toCompletion (incl M₁ M₂).toCompletion :=
  burnsideF48t_qe_of_core (burnsideF48t_ecore hF hconj) θ hA hM1 hM2 hgen β hβ hcard haM hbM
    hK'le (by rw [← hK'card]; exact Nat.card_congr (Equiv.subtypeEquiv θ.toEquiv fun z => Iff.rfl))
    haK hbK ha2 hb2 hrel

end CFSG.ASVolI
