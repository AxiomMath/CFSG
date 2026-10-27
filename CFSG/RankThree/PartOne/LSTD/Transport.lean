module

public import CFSG.RankThree.PartOne.CTP.LStd

public section

namespace CFSG.RankThree.PartOne.LSTD

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP CFSG.Assembly.LowTwoRank

variable {P G : Type} [Group P] [Group G]

theorem map_inf_of_injective {θ : P →* G} (hθ : Function.Injective θ) (A B : Subgroup P) :
    (A ⊓ B).map θ = A.map θ ⊓ B.map θ :=
  (Subgroup.map_inf_eq A B θ hθ)

theorem map_inf_centralizer_of_injective {θ : P →* G} (hθ : Function.Injective θ)
    (B J : Subgroup P) :
    B.map θ ⊓ Subgroup.centralizer (J.map θ : Set G) =
      (B ⊓ Subgroup.centralizer (J : Set P)).map θ := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, ⟨hy, fun j hj => ?_⟩, rfl⟩
    have := hc (θ j) ⟨j, hj, rfl⟩
    exact hθ (by simpa using this)
  · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    have := hc j hj
    simpa using congrArg θ this

theorem map_conjBy (θ : P →* G) (w : P) (H : Subgroup P) :
    (conjBy w H).map θ = conjBy (θ w) (H.map θ) := by
  unfold conjBy
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem map_mem_normalizer {θ : P →* G} {B : Subgroup P} {x : P}
    (hx : x ∈ Subgroup.normalizer (B : Set P)) :
    θ x ∈ Subgroup.normalizer ((B.map θ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨x * z * x⁻¹, (hx z).mp hz, by simp⟩
  · rintro ⟨z, hz, hzy⟩
    have h1 : y = θ x⁻¹ * θ z * θ x := by
      rw [map_inv, hzy]
      group
    rw [h1]
    have hz' : x⁻¹ * z * x ∈ B := by
      have := (hx (x⁻¹ * z * x)).mpr (by simpa [mul_assoc] using hz)
      exact this
    exact ⟨x⁻¹ * z * x, hz', by simp⟩

theorem StdTriangle.map {f₀ : ℕ} {K : Subgroup P} {J : Fin 3 → Fin 3 → Subgroup P}
    {BK : Subgroup P} (S : StdTriangle f₀ K J BK) (θ : P →* G) (hθ : Function.Injective θ) :
    StdTriangle f₀ (K.map θ) (fun a b => (J a b).map θ) (BK.map θ) := by
  obtain ⟨Kq, hKq, h, φ, hJ, hBK, hT⟩ := S
  let e : ↥(K.map θ) ≃* ↥K := (Subgroup.equivMapOfInjective K θ hθ).symm
  have he : ∀ x : ↥(K.map θ), θ ((e x : ↥K) : P) = (x : G) := fun x =>
    congrArg Subtype.val ((Subgroup.equivMapOfInjective K θ hθ).apply_symm_apply x)
  refine ⟨Kq, hKq, h, e.trans φ, fun a b hab => ⟨?_, fun x => ?_⟩, ?_, fun x => ?_⟩
  · exact Subgroup.map_mono (hJ a b hab).1
  · have h1 : (x : G) ∈ (J a b).map θ ↔ ((e x : ↥K) : P) ∈ J a b := by
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = ((e x : ↥K) : P) := hθ (by rw [hyx, he])
        rw [← this]
        exact hy
      · intro hy
        exact ⟨_, hy, he x⟩
    rw [h1]
    exact (hJ a b hab).2 (e x)
  · exact Subgroup.map_mono hBK
  · have h1 : (x : G) ∈ BK.map θ ↔ ((e x : ↥K) : P) ∈ BK := by
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = ((e x : ↥K) : P) := hθ (by rw [hyx, he])
        rw [← this]
        exact hy
      · intro hy
        exact ⟨_, hy, he x⟩
    rw [h1]
    exact hT (e x)

def LFam.map {L B : Subgroup P} {f₀ : ℕ} {b : P} {K : Subgroup P} (S : LFam L B f₀ b K)
    (θ : P →* G) (hθ : Function.Injective θ) :
    LFam (L.map θ) (B.map θ) f₀ (θ b) (K.map θ) where
  W := θ.comp S.W
  J a b := (S.J a b).map θ
  W_L σ := ⟨S.W σ, S.W_L σ, rfl⟩
  W_B σ := map_mem_normalizer (S.W_B σ)
  J_symm a b := by rw [S.J_symm a b]
  J_equiv σ a b := by
    rw [S.J_equiv σ a b, map_conjBy]
    rfl
  J_model a b hab := by
    obtain ⟨e⟩ : Nonempty (↥((S.J a b).map θ) ≃* ↥(S.J a b)) :=
      ⟨(Subgroup.equivMapOfInjective (S.J a b) θ hθ).symm⟩
    exact Equivariance.statedClassicalModel_of_mulEquiv e.symm (S.J_model a b hab)
  B_elem := Equivariance.isElementaryAbelian_map S.B_elem θ
  B_card := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective B θ hθ).toEquiv.symm]
    exact S.B_card
  line_card a b hab := by
    rw [← map_inf_of_injective hθ,
      Nat.card_congr (Subgroup.equivMapOfInjective (B ⊓ S.J a b) θ hθ).toEquiv.symm]
    exact S.line_card a b hab
  hyper_ne a b d e hab hde hne := by
    rw [map_inf_centralizer_of_injective hθ, map_inf_centralizer_of_injective hθ]
    intro h
    exact S.hyper_ne a b d e hab hde hne (Subgroup.map_injective hθ h)
  B_gen := by
    rw [← map_inf_of_injective hθ, ← map_inf_of_injective hθ, ← map_inf_of_injective hθ,
      ← map_inf_of_injective hθ, ← Subgroup.map_sup, ← Subgroup.map_sup, ← Subgroup.map_sup]
    congr 1
    exact S.B_gen
  disj a b d e hab hde had hae hbd hbe := by
    have h := S.disj a b d e hab hde had hae hbd hbe
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (h hx) y hy
    simpa using congrArg θ this
  K_eq := (congrArg (Subgroup.map θ) S.K_eq).trans (Subgroup.map_sup _ _ _)
  b_mem := by
    rw [← map_inf_of_injective hθ]
    exact ⟨b, S.b_mem, rfl⟩
  b_ne := fun h => S.b_ne (hθ (by rw [h, map_one]))
  BK_card := by
    rw [← map_inf_of_injective hθ,
      Nat.card_congr (Subgroup.equivMapOfInjective (B ⊓ K) θ hθ).toEquiv.symm]
    exact S.BK_card
  hyper_eq x y hxy := by
    have h := S.hyper_eq x y hxy
    have e1 : (B.map θ) ⊓ Subgroup.centralizer (((S.J (e3 x) (e3 y)).map θ : Subgroup G) : Set G) =
        (B ⊓ Subgroup.centralizer (S.J (e3 x) (e3 y) : Set P)).map θ :=
      map_inf_centralizer_of_injective hθ _ _
    have e2 : (B.map θ) ⊓ (K.map θ) ⊓ Subgroup.centralizer
        (((S.J (e3 x) (e3 y)).map θ : Subgroup G) : Set G) =
        (B ⊓ K ⊓ Subgroup.centralizer (S.J (e3 x) (e3 y) : Set P)).map θ := by
      rw [← map_inf_of_injective hθ B K]
      exact map_inf_centralizer_of_injective hθ (B ⊓ K) _
    rw [e1, e2, ← MonoidHom.map_zpowers, ← Subgroup.map_sup, h]
  std := by
    have := StdTriangle.map S.std θ hθ
    rwa [← map_inf_of_injective hθ B K]

end CFSG.RankThree.PartOne.LSTD
