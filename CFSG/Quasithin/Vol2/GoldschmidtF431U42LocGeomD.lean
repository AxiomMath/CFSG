module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LocKlein

public section

namespace CFSG.Quasithin.H13.F431.U42

theorem mem_map_conj {G : Type*} [Group G] {W : Subgroup G} {c x : G} :
    x ∈ W.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ W := by
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [mul_assoc] using hw
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem map_conj_map_conj {G : Type*} [Group G] (W : Subgroup G) (g k : G) :
    (W.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      W.map (MulAut.conj (g * k)).toMonoidHom := by
  ext x
  rw [mem_map_conj, mem_map_conj, mem_map_conj]
  have : (g * k)⁻¹ * x * (g * k) = k⁻¹ * (g⁻¹ * x * g) * k := by group
  rw [this]

structure GeomData (G : Type) [Group G] where
  V2 : Subgroup G
  t : G
  u0 : G
  u15 : G
  u20 : G
  u24 : G
  Pt : G → Prop
  Ln : Subgroup G → Prop
  Q : Subgroup G
  hVab : ∀ a ∈ V2, ∀ b ∈ V2, a * b = b * a
  ht : t ∈ V2
  ht2 : t * t = 1
  hu0 : u0 ∈ V2
  hu15 : u15 ∈ V2
  hu20 : u20 ∈ V2
  hu24 : u24 ∈ V2
  hu0sq : u0 * u0 = 1
  hu15sq : u15 * u15 = 1
  hu20sq : u20 * u20 = 1
  hu24sq : u24 * u24 = 1
  hrel : u0 * u20 = u24 * t
  hu15ne : u15 ≠ 1
  hPt : ∀ g u : G, Pt u → Pt (g * u * g⁻¹)
  hLn : ∀ (g : G) (W : Subgroup G), Ln W → Ln (W.map (MulAut.conj g).toMonoidHom)
  hLnV : Ln V2
  hPt0 : Pt u0
  hPt15 : Pt u15
  hPt20 : Pt u20
  hPt24 : Pt u24
  hnPt : ¬ Pt t
  hnPt0 : ¬ Pt (u0 * t)
  hnPt20 : ¬ Pt (u20 * t)
  hnPt24 : ¬ Pt (u24 * t)
  line_unique : ∀ u : G, Pt u → u * t = t * u → ∀ W W' : Subgroup G, Ln W → Ln W' → u ∈ W →
    t ∈ W → u ∈ W' → t ∈ W' → W = W'
  line_comm : ∀ u u' : G, Pt u → Pt u' → u * t = t * u → u' * t = t * u' → u * u' = u' * u →
    ∀ W : Subgroup G, Ln W → u ∈ W → t ∈ W → u' ∈ W
  hXact : ∀ h ∈ Subgroup.normalizer (V2 : Set G), h * t * h⁻¹ = t →
    h * u15 * h⁻¹ = u15 ∨ h * u15 * h⁻¹ = u15 * t
  hQp : IsPGroup 2 Q
  hQm : ∀ Q' : Subgroup G, Q' ≤ Subgroup.centralizer ({t} : Set G) → IsPGroup 2 Q' → Q ≤ Q' →
    Q' = Q
  hQH : Q ≤ Subgroup.centralizer ({t} : Set G)
  htQ : t ∈ Q
  hu15Q : u15 ∈ Q
  hQz : ∀ q ∈ Q, q * u0 = u0 * q
  hQact : ∀ q ∈ Q, q * u15 * q⁻¹ = u15 ∨ q * u15 * q⁻¹ = u15 * t
  hX1 : ∀ K : Subgroup G,
    K ≤ Subgroup.normalizer (V2 : Set G) ⊓ Subgroup.centralizer ({t} : Set G) →
    (∀ e ∈ Subgroup.normalizer (V2 : Set G) ⊓ Subgroup.centralizer ({t} : Set G),
      ∀ k ∈ K, e * k * e⁻¹ ∈ K) → Subgroup.zpowers t ≤ K → ¬ 4 ∣ Nat.card K →
    K = Subgroup.zpowers t

end CFSG.Quasithin.H13.F431.U42
