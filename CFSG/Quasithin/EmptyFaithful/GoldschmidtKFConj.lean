module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFTwo

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def centralizerConjEquiv {G : Type} [Group G] (σ k : G) :
    ↥(Subgroup.centralizer ({σ} : Set G)) ≃*
      ↥(Subgroup.centralizer ({k⁻¹ * σ * k} : Set G)) where
  toFun c := ⟨k⁻¹ * (c : G) * k, by
    have h := Subgroup.mem_centralizer_singleton_iff.mp c.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc k⁻¹ * (c : G) * k * (k⁻¹ * σ * k) = k⁻¹ * ((c : G) * σ) * k := by group
      _ = k⁻¹ * (σ * (c : G)) * k := by rw [h]
      _ = k⁻¹ * σ * k * (k⁻¹ * (c : G) * k) := by group⟩
  invFun d := ⟨k * (d : G) * k⁻¹, by
    have h := Subgroup.mem_centralizer_singleton_iff.mp d.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' : (d : G) * (k⁻¹ * σ * k) = (k⁻¹ * σ * k) * (d : G) := h
    calc k * (d : G) * k⁻¹ * σ = k * ((d : G) * (k⁻¹ * σ * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * σ * k) * (d : G)) * k⁻¹ := by rw [h']
      _ = σ * (k * (d : G) * k⁻¹) := by group⟩
  left_inv c := Subtype.ext (by group)
  right_inv d := Subtype.ext (by group)
  map_mul' a b := Subtype.ext (by
    change k⁻¹ * ((a : G) * (b : G)) * k = k⁻¹ * (a : G) * k * (k⁻¹ * (b : G) * k)
    group)

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
  {X : Subgroup G} {τ f : G}

theorem KFHyp.oddCore_centralizer_conj (h113 : StageLemma14113)
    (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) {x k : G} (hk : k⁻¹ * (τ * f) * k = x) :
    ∃ F' : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F' ∧ Nat.card ↥F' = 9 ∧
      ((CFSG.pPrimeCore 2 ↥(Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype) ≤ F' := by
  subst hk
  obtain ⟨F, -, hFel, hF9, -, hQF⟩ := h.oddCore_centralizer_sigma h113
  refine ⟨F.map (MulAut.conj k⁻¹).toMonoidHom, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_, ?_⟩
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
    apply Subtype.ext
    have := congrArg (fun w : ↥F => (w : G)) (hFel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    change (MulAut.conj k⁻¹) a * (MulAut.conj k⁻¹) b = (MulAut.conj k⁻¹) b * (MulAut.conj k⁻¹) a
    rw [← map_mul, ← map_mul]
    exact congrArg (MulAut.conj k⁻¹) this
  · rintro _ ⟨a, ha, rfl⟩
    change ((MulAut.conj k⁻¹) a) ^ 3 = 1
    rw [← map_pow, hFel.2 a ha, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hF9]
  · intro y hy
    obtain ⟨d, hd, rfl⟩ := hy
    have hmap := CFSG.pPrimeCore_map_iso 2 (centralizerConjEquiv (τ * f) k)
    rw [← hmap] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    refine ⟨(c : G), hQF ⟨c, hc, rfl⟩, ?_⟩
    change k⁻¹ * (c : G) * k⁻¹⁻¹ = k⁻¹ * (c : G) * k
    rw [inv_inv]

theorem KFHyp.exists_conj_sigma_tau (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) :
    ∃ k : G, k⁻¹ * (τ * f) * k = τ := by
  obtain ⟨t₀, -, -, h2⟩ := h.ht₀
  exact ⟨t₀⁻¹, by rw [inv_inv]; exact h2⟩

theorem KFHyp.exists_conj_sigma_f (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f)
    (hg : ∃ g : G, g⁻¹ * τ * g = f) : ∃ k : G, k⁻¹ * (τ * f) * k = f := by
  obtain ⟨t₀, -, -, h2⟩ := h.ht₀
  obtain ⟨g, hg⟩ := hg
  refine ⟨t₀⁻¹ * g, ?_⟩
  calc (t₀⁻¹ * g)⁻¹ * (τ * f) * (t₀⁻¹ * g) = g⁻¹ * (t₀ * (τ * f) * t₀⁻¹) * g := by group
    _ = f := by rw [h2, hg]

theorem KFHyp.exists_conj_sigma {x : G} (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f)
    (hg : ∃ g : G, g⁻¹ * τ * g = f) (hx : x = τ ∨ x = f) : ∃ k : G, k⁻¹ * (τ * f) * k = x := by
  rcases hx with rfl | rfl
  · exact h.exists_conj_sigma_tau
  · exact h.exists_conj_sigma_f hg

end CFSG.Quasithin.SBd19F
