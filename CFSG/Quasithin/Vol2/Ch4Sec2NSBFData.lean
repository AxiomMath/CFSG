module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFRho
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBFAlg
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKRF

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G} {m k n j : ℕ}

private theorem mat_add_self_nsbfd (A : Matrix (Fin n) (Fin n) (ZMod 2)) : A + A = 0 := by
  ext a b
  simp only [Matrix.add_apply, Matrix.zero_apply]
  have h : ∀ c : ZMod 2, c + c = 0 := by decide
  exact h _

private theorem mat_neg_self_nsbfd (A : Matrix (Fin n) (Fin n) (ZMod 2)) : -A = A := by
  ext a b
  simp only [Matrix.neg_apply]
  have h : ∀ c : ZMod 2, -c = c := by decide
  exact h _

section Comm

variable {D : StdData G T L I K m k n j} {ρ : G → Matrix (Fin n) (Fin n) (ZMod 2)}

theorem comm_data (hρ : IsRho D ρ) {g : G} (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) {u v : G} (hu : u ∈ uZero I K)
    (hv : v ∈ uZero I K) :
    (u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹ ∈ uZero I K ∧
      coG D (u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹) =
        actM (ρ (g⁻¹ * v * g) + 1) (coG D u)) ∧
    (g * (u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ ∈ uZero I K ∧
      coG D (g * (u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹) =
        actM (ρ (g * u * g⁻¹) + 1) (coG D v)) := by
  refine ⟨coG_comm_left hρ hu (h1 v hv), ?_⟩
  have hform : g * (u * (g⁻¹ * v * g) * u⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ =
      (g * u * g⁻¹) * v * (g * u * g⁻¹)⁻¹ * v⁻¹ := by group
  rw [hform]
  exact coG_comm_right hρ hv (h2 u hu)

noncomputable def Pfun (D : StdData G T L I K m k n j) (ρ : G → Matrix (Fin n) (Fin n) (ZMod 2))
    (g : G) (Y : Fin j → Fin n → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  ρ (g⁻¹ * zEn D Y * g) + 1

theorem Pfun_mul_zero (hj : 0 < j) (hρ : IsRho D ρ) {g : G}
    (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) (Y₁ Y₂ : Fin j → Fin n → ZMod 2) :
    Pfun D ρ g Y₁ * Pfun D ρ g Y₂ = 0 := by
  apply eq_zero_of_actM_eq_zero hj
  intro Y
  set u := zEn D Y with hu
  set v₁ := zEn D Y₁ with hv₁
  set v₂ := zEn D Y₂ with hv₂
  have hu' : u ∈ uZero I K := zEn_mem D Y
  have hv₁' : v₁ ∈ uZero I K := zEn_mem D Y₁
  have hv₂' : v₂ ∈ uZero I K := zEn_mem D Y₂
  obtain ⟨⟨hc₀, hcc₀⟩, ⟨hgc₀, -⟩⟩ := comm_data hρ h1 h2 hu' hv₂'
  set c₀ := u * (g⁻¹ * v₂ * g) * u⁻¹ * (g⁻¹ * v₂ * g)⁻¹ with hc₀def
  set z₁ := g⁻¹ * v₁ * g with hz₁
  have hz₁R : z₁ ∈ pCoreOf 2 I := h1 v₁ hv₁'
  have hcomm : z₁ * c₀ = c₀ * z₁ := by
    have hw := uZero_comm D hv₁' hgc₀
    have e1 : z₁ * c₀ = g⁻¹ * (v₁ * (g * c₀ * g⁻¹)) * g := by simp only [hz₁]; group
    have e2 : c₀ * z₁ = g⁻¹ * ((g * c₀ * g⁻¹) * v₁) * g := by simp only [hz₁]; group
    rw [e1, e2, hw]
  have hfix : z₁ * c₀ * z₁⁻¹ = c₀ := by
    rw [hcomm, mul_inv_cancel_right]
  obtain ⟨-, hz₁c⟩ := hρ z₁ hz₁R c₀ hc₀
  rw [hfix] at hz₁c
  have hY : actM (Pfun D ρ g Y₂) Y = coG D c₀ := by
    rw [hcc₀, coG_zEn]
    rfl
  rw [actM_mul, hY]
  show actM (ρ z₁ + 1) (coG D c₀) = 0
  rw [actM_add_left, actM_one, ← hz₁c]
  exact tm_add_self _

theorem Pfun_add (hj : 0 < j) (hρ : IsRho D ρ) {g : G}
    (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I) (Y₁ Y₂ : Fin j → Fin n → ZMod 2) :
    Pfun D ρ g (Y₁ + Y₂) = Pfun D ρ g Y₁ + Pfun D ρ g Y₂ := by
  have hr₁ : g⁻¹ * zEn D Y₁ * g ∈ pCoreOf 2 I := h1 _ (zEn_mem D Y₁)
  have hr₂ : g⁻¹ * zEn D Y₂ * g ∈ pCoreOf 2 I := h1 _ (zEn_mem D Y₂)
  have hprod : g⁻¹ * zEn D (Y₁ + Y₂) * g = (g⁻¹ * zEn D Y₁ * g) * (g⁻¹ * zEn D Y₂ * g) := by
    rw [zEn_add]
    group
  have h0 := Pfun_mul_zero hj hρ h1 h2 Y₁ Y₂
  unfold Pfun at h0 ⊢
  rw [hprod, rho_mul_nsbfr hj hρ hr₁ hr₂]
  set a := ρ (g⁻¹ * zEn D Y₁ * g)
  set b := ρ (g⁻¹ * zEn D Y₂ * g)
  have hexp : (a + 1) * (b + 1) = a * b + a + b + 1 := by noncomm_ring
  rw [hexp] at h0
  have h3 : a * b + 1 = a + b := by
    have h4 : (a * b + 1) + (a + b) = 0 := by rw [← h0]; abel
    have := eq_neg_of_add_eq_zero_left h4
    rw [this, mat_neg_self_nsbfd]
  rw [h3]
  have h11 : (1 : Matrix (Fin n) (Fin n) (ZMod 2)) + 1 = 0 := mat_add_self_nsbfd 1
  calc a + b = (a + b) + 0 := (add_zero _).symm
    _ = (a + b) + (1 + 1) := by rw [h11]
    _ = (a + 1) + (b + 1) := by abel

end Comm

section Interface

variable {D : StdData G T L I K m k n j}

theorem exists_nonfix_of_h3 (h22 : ASC22Three G) (hc : Conf4212 G T M L I H K) (hIH : I ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hn : 0 < n) (hj : 0 < j)
    (D : StdData G T L I K m k n j) (hRΓ : pCoreOf 2 I ≤ gammaZero T M L I) {g : G}
    (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h3 : ∃ u ∈ uZero I K, g⁻¹ * u * g ∉ kerA (K ⊔ pCoreOf 2 I) (gammaZero T M L I)) :
    ∃ u ∈ uZero I K, ∃ z ∈ uZero I K, (g⁻¹ * u * g) * z * (g⁻¹ * u * g)⁻¹ ≠ z := by
  obtain ⟨u, hu, hnot⟩ := h3
  refine ⟨u, hu, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hnot
  have hr := h1 u hu
  have hnormU : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (uZero I K : Set G) :=
    le_normalizer_uZero hIH hHK
  refine ⟨Subgroup.mem_sup_right hr, fun a ha => ?_⟩
  apply hRΓ
  refine centralizer_uZero_le h22 hc hIH hHK hn hj D
    ((K ⊔ pCoreOf 2 I).mul_mem ((K ⊔ pCoreOf 2 I).mul_mem ((K ⊔ pCoreOf 2 I).inv_mem ha)
      (Subgroup.mem_sup_right hr)) ha) ?_
  intro z hz
  have hz2 : a * z * a⁻¹ ∈ uZero I K := (Subgroup.mem_normalizer_iff.mp (hnormU ha) z).mp hz
  have h := hcon _ hz2
  calc a⁻¹ * (g⁻¹ * u * g) * a * z * (a⁻¹ * (g⁻¹ * u * g) * a)⁻¹
      = a⁻¹ * ((g⁻¹ * u * g) * (a * z * a⁻¹) * (g⁻¹ * u * g)⁻¹) * a := by group
    _ = a⁻¹ * (a * z * a⁻¹) * a := by rw [h]
    _ = z := by group

theorem exists_flipHyp (hn : 0 < n) (hj : 0 < j) (hIH : I ≤ H)
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (D : StdData G T L I K m k n j) {g : G}
    (h1 : ∀ u ∈ uZero I K, g⁻¹ * u * g ∈ pCoreOf 2 I)
    (h2 : ∀ u ∈ uZero I K, g * u * g⁻¹ ∈ pCoreOf 2 I)
    (hP0 : ∃ u ∈ uZero I K, ∃ z ∈ uZero I K, (g⁻¹ * u * g) * z * (g⁻¹ * u * g)⁻¹ ≠ z) :
    ∃ F : FlipHyp j n,
      (∀ Y, Y ∈ F.S ↔ ∃ c ∈ uZero I K, g * c * g⁻¹ ∈ uZero I K ∧ coG D c = Y) ∧
      (∀ c ∈ uZero I K, g * c * g⁻¹ ∈ uZero I K → F.T (coG D c) = coG D (g * c * g⁻¹)) := by
  classical
  obtain ⟨ρ, hρ⟩ := exists_rho hIH hHK hn hj D
  have h1' : ∀ u ∈ uZero I K, g⁻¹⁻¹ * u * g⁻¹ ∈ pCoreOf 2 I := by
    intro u hu
    rw [inv_inv]
    exact h2 u hu
  have h2' : ∀ u ∈ uZero I K, g⁻¹ * u * g⁻¹⁻¹ ∈ pCoreOf 2 I := by
    intro u hu
    rw [inv_inv]
    exact h1 u hu
  let P : (Fin j → Fin n → ZMod 2) →+ Matrix (Fin n) (Fin n) (ZMod 2) :=
    AddMonoidHom.mk' (Pfun D ρ g) (Pfun_add hj hρ h1 h2)
  let Q : (Fin j → Fin n → ZMod 2) →+ Matrix (Fin n) (Fin n) (ZMod 2) :=
    AddMonoidHom.mk' (Pfun D ρ g⁻¹) (Pfun_add hj hρ h1' h2')
  have hPapp : ∀ Y, P Y = ρ (g⁻¹ * zEn D Y * g) + 1 := fun Y => rfl
  have hQapp : ∀ Y, Q Y = ρ (g * zEn D Y * g⁻¹) + 1 := fun Y => by
    show ρ (g⁻¹⁻¹ * zEn D Y * g⁻¹) + 1 = _
    rw [inv_inv]
  let S : AddSubgroup (Fin j → Fin n → ZMod 2) :=
    { carrier := {Y | ∃ c ∈ uZero I K, g * c * g⁻¹ ∈ uZero I K ∧ coG D c = Y}
      add_mem' := by
        rintro _ _ ⟨c₁, hc₁, hgc₁, rfl⟩ ⟨c₂, hc₂, hgc₂, rfl⟩
        refine ⟨c₁ * c₂, mul_mem hc₁ hc₂, ?_, coG_mul D hc₁ hc₂⟩
        have : g * (c₁ * c₂) * g⁻¹ = (g * c₁ * g⁻¹) * (g * c₂ * g⁻¹) := by group
        rw [this]
        exact mul_mem hgc₁ hgc₂
      zero_mem' := ⟨1, one_mem _, by simpa using one_mem _, coG_one D⟩
      neg_mem' := by
        rintro _ ⟨c, hc, hgc, rfl⟩
        exact ⟨c, hc, hgc, (tm_neg_eq_self _).symm⟩ }
  have hSmem : ∀ Y, Y ∈ S ↔ ∃ c ∈ uZero I K, g * c * g⁻¹ ∈ uZero I K ∧ coG D c = Y :=
    fun Y => Iff.rfl
  let Tm : (Fin j → Fin n → ZMod 2) → (Fin j → Fin n → ZMod 2) :=
    fun Y => coG D (g * zEn D Y * g⁻¹)
  have hTcoG : ∀ c ∈ uZero I K, g * c * g⁻¹ ∈ uZero I K →
      Tm (coG D c) = coG D (g * c * g⁻¹) := by
    intro c hc hgc
    show coG D (g * zEn D (coG D c) * g⁻¹) = _
    rw [zEn_coG D hc]
  have hcd : ∀ Y Y' : Fin j → Fin n → ZMod 2,
      ∃ c₀ ∈ uZero I K, g * c₀ * g⁻¹ ∈ uZero I K ∧ coG D c₀ = actM (P Y') Y ∧
        coG D (g * c₀ * g⁻¹) = actM (Q Y) Y' := by
    intro Y Y'
    obtain ⟨⟨hc₀, hcc₀⟩, ⟨hgc₀, hgcc₀⟩⟩ :=
      comm_data hρ h1 h2 (zEn_mem D Y) (zEn_mem D Y')
    refine ⟨_, hc₀, hgc₀, ?_, ?_⟩
    · rw [hcc₀, coG_zEn, hPapp]
    · rw [hgcc₀, coG_zEn, hQapp]
  refine ⟨{ P := P
            Q := Q
            S := S
            T := Tm
            PP := ?_
            P0 := ?_
            Sm := ?_
            Tadd := ?_
            Tinj := ?_
            TQ := ?_ }, hSmem, ?_⟩
  · intro Y₁ Y₂
    exact Pfun_mul_zero hj hρ h1 h2 Y₁ Y₂
  · obtain ⟨u, hu, z, hz, hne⟩ := hP0
    refine ⟨coG D u, fun h0 => hne ?_⟩
    rw [hPapp, zEn_coG D hu] at h0
    have h1' : ρ (g⁻¹ * u * g) = 1 := by
      have := eq_neg_of_add_eq_zero_left h0
      rw [this, mat_neg_self_nsbfd]
    exact (rho_eq_one_iff_nsbfr hj hρ (h1 u hu)).mp h1' z hz
  · intro Y Y'
    obtain ⟨c₀, hc₀, hgc₀, hcc₀, -⟩ := hcd Y Y'
    exact ⟨c₀, hc₀, hgc₀, hcc₀⟩
  · intro s₁ hs₁ s₂ hs₂
    obtain ⟨c₁, hc₁, hgc₁, rfl⟩ := hs₁
    obtain ⟨c₂, hc₂, hgc₂, rfl⟩ := hs₂
    rw [← coG_mul D hc₁ hc₂, hTcoG _ (mul_mem hc₁ hc₂) (by
      have : g * (c₁ * c₂) * g⁻¹ = (g * c₁ * g⁻¹) * (g * c₂ * g⁻¹) := by group
      rw [this]
      exact mul_mem hgc₁ hgc₂), hTcoG _ hc₁ hgc₁, hTcoG _ hc₂ hgc₂]
    have : g * (c₁ * c₂) * g⁻¹ = (g * c₁ * g⁻¹) * (g * c₂ * g⁻¹) := by group
    rw [this, coG_mul D hgc₁ hgc₂]
  · intro s₁ hs₁ s₂ hs₂ h
    obtain ⟨c₁, hc₁, hgc₁, rfl⟩ := hs₁
    obtain ⟨c₂, hc₂, hgc₂, rfl⟩ := hs₂
    rw [hTcoG _ hc₁ hgc₁, hTcoG _ hc₂ hgc₂] at h
    have h1 := coG_injOn D hgc₁ hgc₂ h
    have h2 : c₁ = c₂ := by
      have := congrArg (fun x => g⁻¹ * x * g) h1
      simpa using this
    rw [h2]
  · intro Y Y'
    obtain ⟨c₀, hc₀, hgc₀, hcc₀, hgcc₀⟩ := hcd Y Y'
    rw [← hcc₀, hTcoG _ hc₀ hgc₀, hgcc₀]
  · exact hTcoG

end Interface

end CFSG.Quasithin.H13.Ch4.NSB
