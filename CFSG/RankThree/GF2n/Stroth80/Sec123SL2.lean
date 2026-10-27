module

public import CFSG.RankThree.GF2n.Stroth80.Sec123SL2Grp
public import CFSG.RankThree.GF2n.Stroth80.Sec123SL2Coord
public import CFSG.RankThree.GF2n.Stroth80.Sec123Fpf
public import CFSG.RankThree.GF2n.Stroth80.Satz5Stroth
public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open TauCeti.QuadraticMap
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

structure ActionData (hc : Ctx M Q Z B) (M₀ : Tim79.QuadModel Q Z K γ) where
  Ψ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)
  C : ↥M → ((M₀.E ≃ₗ[K] M₀.E) ≃* (M₀.E ≃ₗ[K] M₀.E))
  hΨπ : ∀ (l : H0 M Z) (x : G), x ∈ Q → M₀.π ((l : G) * x * (l : G)⁻¹) = Ψ l (M₀.π x)
  hΨker : ∀ l : H0 M Z, Ψ l = 1 ↔ (l : G) ∈ Q
  hΨiso : ∀ l e, M₀.Qf (Ψ l e) = M₀.Qf e
  hΨC : ∀ (m : ↥M) (l : ↥(H0 M Z)),
    Ψ ⟨(m : G) * l * (m : G)⁻¹, hc.conj_mem_H0 m.2 l.2⟩ = C m (Ψ l)
  hCmul : ∀ (m m' : ↥M) g, C (m * m') g = C m (C m' g)
  hCJ : ∀ m : ↥M, (⁅orthogonalGroup M₀.toQuadraticForm,
      orthogonalGroup M₀.toQuadraticForm⁆).map (C m).toMonoidHom =
    ⁅orthogonalGroup M₀.toQuadraticForm, orthogonalGroup M₀.toQuadraticForm⁆

theorem exists_actionData (hc : Ctx M Q Z B) (h : GlobalModelData M Q Z γ M₀) :
    Nonempty (ActionData hc M₀) := by
  obtain ⟨Ψ, hΨπ, hΨker, hΨiso⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨φ, hφπ, -, hφadd, -⟩ := exists_actionHom_M hc.hyp h
  have hQconj : ∀ (m : G), m ∈ M → ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := fun m hm x hx =>
    (hc.conj_mem_Q_of_mem_M hm).1 x hx
  have hsim : ∀ m : ↥M, ∃ (σ : K ≃+* K) (a : K), a ≠ 0 ∧
      (∀ (c : K) e, φ m (c • e) = σ c • φ m e) ∧
        ∀ e, M₀.Qf (φ m e) = a * σ (M₀.Qf e) := by
    intro m
    obtain ⟨σ, a, T, hT1, hTπ, -, hTQ⟩ := h.act m m.2
    have hφT : (φ m : M₀.E → M₀.E) = T :=
      eq_of_pi_conj_eq (M₀ := M₀) (g := (m : G)) (hφπ m) hTπ
    refine ⟨σ, (a : K), a.ne_zero, fun c e => ?_, fun e => ?_⟩
    · show (φ m : M₀.E → M₀.E) (c • e) = σ c • (φ m : M₀.E → M₀.E) e
      rw [hφT]
      exact hT1 c e
    · show M₀.Qf ((φ m : M₀.E → M₀.E) e) = _
      rw [hφT]
      exact hTQ e
  choose σ a ha hlin hQ using hsim
  let Tadd : ↥M → (M₀.E ≃+ M₀.E) := fun m => { toEquiv := φ m, map_add' := hφadd m }
  have hTadd : ∀ m e, Tadd m e = φ m e := fun m e => rfl
  have hTlin : ∀ m (c : K) e, Tadd m (c • e) = σ m c • Tadd m e := fun m c e => hlin m c e
  refine ⟨⟨Ψ, fun m => SL2Coord.semiConj (σ m) (Tadd m) (hTlin m), hΨπ, hΨker, hΨiso, ?_, ?_, ?_⟩⟩
  · intro m l
    refine LinearEquiv.ext fun e => ?_
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    have hlM : (l : G) ∈ M := l.2.1
    have hy : (m : G)⁻¹ * x * (m : G) ∈ Q := by
      have := hQconj ((m : G)⁻¹) (M.inv_mem m.2) x hx
      simpa using this
    have hly : (l : G) * ((m : G)⁻¹ * x * (m : G)) * (l : G)⁻¹ ∈ Q := hQconj _ hlM _ hy
    have e1 : (Tadd m).symm (M₀.π x) = M₀.π ((m : G)⁻¹ * x * (m : G)) := by
      rw [AddEquiv.symm_apply_eq, hTadd, ← hφπ m _ hy]
      congr 1
      group
    have hL := hΨπ ⟨(m : G) * l * (m : G)⁻¹, hc.conj_mem_H0 m.2 l.2⟩ x hx
    rw [SL2Coord.semiConj_apply, e1, ← hΨπ l _ hy, hTadd, ← hφπ m _ hly, ← hL]
    congr 1
    group
  · intro m m' g
    refine LinearEquiv.ext fun x => ?_
    have hmul : ∀ e, Tadd (m * m') e = Tadd m (Tadd m' e) := fun e => by
      simp only [hTadd, map_mul, Equiv.Perm.mul_apply]
    have hsymm : (Tadd (m * m')).symm x = (Tadd m').symm ((Tadd m).symm x) := by
      rw [AddEquiv.symm_apply_eq, hmul]
      simp
    simp only [SL2Coord.semiConj_apply, hmul, hsymm]
  · intro m
    exact SL2Coord.map_semiConj_commutator (σ m) (Tadd m) (hTlin m) M₀.toQuadraticForm (a m)
      (ha m) (hQ m)

namespace ActionData

variable {hc : Ctx M Q Z B} (D : ActionData hc M₀)

@[expose] def img (X : Subgroup G) : Subgroup (M₀.E ≃ₗ[K] M₀.E) :=
  (X.subgroupOf (H0 M Z)).map D.Ψ

theorem mem_img {X : Subgroup G} {g : M₀.E ≃ₗ[K] M₀.E} :
    g ∈ D.img X ↔ ∃ l : H0 M Z, (l : G) ∈ X ∧ D.Ψ l = g := by
  unfold img
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.mp hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, Subgroup.mem_subgroupOf.mpr hl, rfl⟩

theorem img_mono {X Y : Subgroup G} (h : X ≤ Y) : D.img X ≤ D.img Y := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := D.mem_img.mp hg
  exact D.mem_img.mpr ⟨l, h hl, rfl⟩

theorem img_conj {X : Subgroup G} (hX : X ≤ H0 M Z) (m : ↥M) :
    D.img (conjSubgroup (m : G) X) = (D.img X).map (D.C m).toMonoidHom := by
  ext g
  constructor
  · intro hg
    obtain ⟨l, hl, rfl⟩ := D.mem_img.mp hg
    rw [mem_conjSubgroup] at hl
    have hlH : (m : G)⁻¹ * l * (m : G) ∈ H0 M Z := hX hl
    refine ⟨D.Ψ ⟨(m : G)⁻¹ * l * (m : G), hlH⟩, D.mem_img.mpr ⟨_, hl, rfl⟩, ?_⟩
    show D.C m (D.Ψ ⟨(m : G)⁻¹ * l * (m : G), hlH⟩) = D.Ψ l
    rw [← D.hΨC m ⟨_, hlH⟩]
    congr 1
    apply Subtype.ext
    show (m : G) * ((m : G)⁻¹ * l * (m : G)) * (m : G)⁻¹ = l
    group
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨l, hl, rfl⟩ := D.mem_img.mp hg'
    refine D.mem_img.mpr ⟨⟨(m : G) * l * (m : G)⁻¹, hc.conj_mem_H0 m.2 l.2⟩, ?_, ?_⟩
    · rw [mem_conjSubgroup]
      show (m : G)⁻¹ * ((m : G) * l * (m : G)⁻¹) * (m : G) ∈ X
      have : (m : G)⁻¹ * ((m : G) * l * (m : G)⁻¹) * (m : G) = l := by group
      rw [this]
      exact hl
    · exact D.hΨC m l

theorem range_eq_img {X : Subgroup G} (hX : X ≤ H0 M Z) :
    (D.Ψ.comp (Subgroup.inclusion hX)).range = D.img X := by
  ext g
  constructor
  · rintro ⟨r, rfl⟩
    exact D.mem_img.mpr ⟨Subgroup.inclusion hX r, r.2, rfl⟩
  · intro hg
    obtain ⟨l, hl, rfl⟩ := D.mem_img.mp hg
    exact ⟨⟨l, hl⟩, rfl⟩

theorem card_img {X : Subgroup G} (hQX : Q ≤ X) (hX : X ≤ H0 M Z) :
    Nat.card X = Nat.card Q * Nat.card (D.img X) := by
  have hker : ∀ r : ↥X, (D.Ψ.comp (Subgroup.inclusion hX)) r = 1 ↔ (r : G) ∈ Q :=
    fun r => D.hΨker (Subgroup.inclusion hX r)
  have h1 := card_eq_card_mul_range hQX (D.Ψ.comp (Subgroup.inclusion hX)) hker
  rw [D.range_eq_img hX] at h1
  exact h1

theorem isPGroup_img {X : Subgroup G} (hX : X ≤ H0 M Z) (hX2 : IsPGroup 2 ↥X) :
    IsPGroup 2 ↥(D.img X) := by
  have h := hX2.of_surjective (D.Ψ.comp (Subgroup.inclusion hX)).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  rwa [D.range_eq_img hX] at h

end ActionData

namespace ActionData

variable {hc : Ctx M Q Z B} (D : ActionData hc M₀)

@[expose] def pre (N : Subgroup (M₀.E ≃ₗ[K] M₀.E)) : Subgroup G :=
  (N.comap (D.Ψ.comp (Subgroup.inclusion hc.LB_le_H0'))).map (LB M Q B).subtype

theorem mem_pre {N : Subgroup (M₀.E ≃ₗ[K] M₀.E)} {l : G} :
    l ∈ D.pre N ↔ ∃ hl : l ∈ LB M Q B, D.Ψ (Subgroup.inclusion hc.LB_le_H0' ⟨l, hl⟩) ∈ N := by
  unfold pre
  constructor
  · rintro ⟨l', hl', rfl⟩
    exact ⟨l'.2, hl'⟩
  · rintro ⟨hl, hN⟩
    exact ⟨⟨l, hl⟩, hN, rfl⟩

theorem pre_le (N : Subgroup (M₀.E ≃ₗ[K] M₀.E)) : D.pre N ≤ LB M Q B := by
  intro l hl
  exact (D.mem_pre.mp hl).1

theorem Q_le_pre (N : Subgroup (M₀.E ≃ₗ[K] M₀.E)) : Q ≤ D.pre N := by
  intro q hq
  have hqL : q ∈ LB M Q B := sec39_Q_le_LB hq
  refine D.mem_pre.mpr ⟨hqL, ?_⟩
  have : D.Ψ (Subgroup.inclusion hc.LB_le_H0' ⟨q, hqL⟩) = 1 :=
    (D.hΨker _).mpr hq
  rw [this]
  exact N.one_mem

theorem img_pre (N : Subgroup (M₀.E ≃ₗ[K] M₀.E)) :
    D.img (D.pre N) = N ⊓ D.img (LB M Q B) := by
  ext g
  constructor
  · intro hg
    obtain ⟨l, hl, rfl⟩ := D.mem_img.mp hg
    obtain ⟨hlL, hlN⟩ := D.mem_pre.mp hl
    exact ⟨hlN, D.mem_img.mpr ⟨l, hlL, rfl⟩⟩
  · rintro ⟨hgN, hg⟩
    obtain ⟨l, hl, rfl⟩ := D.mem_img.mp hg
    exact D.mem_img.mpr ⟨l, D.mem_pre.mpr ⟨hl, hgN⟩, rfl⟩

end ActionData

theorem finite_linearEquiv_model (M₀ : Tim79.QuadModel Q Z K γ) : Finite (M₀.E ≃ₗ[K] M₀.E) := by
  haveI : Module.Finite K M₀.E := M₀.fin
  haveI : Finite M₀.E := Module.finite_of_finite K
  exact Finite.of_injective (fun f : M₀.E ≃ₗ[K] M₀.E => (f : M₀.E → M₀.E))
    (fun f g h => LinearEquiv.ext (congrFun h))

namespace ActionData

variable {hc : Ctx M Q Z B} (D : ActionData hc M₀)

theorem card_inf_img_dvd (hw : Width Q Z 2) {τ' : G} (hτ'M : τ' ∈ M)
    (hord : orderOf τ' = Nat.card Z - 1)
    (hτ'L : ∀ l ∈ LB M Q B, τ' * l * τ'⁻¹ ∈ LB M Q B)
    (hfree : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ l ∈ LB M Q B,
      τ' ^ i * l * (τ' ^ i)⁻¹ * l⁻¹ ∈ Q → l ∈ Q)
    (N : Subgroup (M₀.E ≃ₗ[K] M₀.E)) (hN : ∀ g ∈ N, D.C ⟨τ', hτ'M⟩ g ∈ N) :
    Nat.card Z - 1 ∣ Nat.card ↥(N ⊓ D.img (LB M Q B)) - 1 := by
  classical
  have hpre : D.pre N ≤ H0 M Z := (D.pre_le N).trans hc.LB_le_H0'
  have hcard := D.card_img (D.Q_le_pre N) hpre
  rw [D.img_pre N] at hcard
  have hτL : ∀ l ∈ D.pre N, τ' * l * τ'⁻¹ ∈ D.pre N := by
    intro l hl
    obtain ⟨hlL, hlN⟩ := D.mem_pre.mp hl
    have h1 := hτ'L l hlL
    refine D.mem_pre.mpr ⟨h1, ?_⟩
    have h2 := D.hΨC ⟨τ', hτ'M⟩ (Subgroup.inclusion hc.LB_le_H0' ⟨l, hlL⟩)
    have e : Subgroup.inclusion hc.LB_le_H0' ⟨τ' * l * τ'⁻¹, h1⟩ =
        ⟨((⟨τ', hτ'M⟩ : ↥M) : G) * ((Subgroup.inclusion hc.LB_le_H0' ⟨l, hlL⟩ : ↥(H0 M Z)) : G) *
          ((⟨τ', hτ'M⟩ : ↥M) : G)⁻¹, hc.conj_mem_H0 hτ'M (Subgroup.inclusion hc.LB_le_H0' _).2⟩ :=
      Subtype.ext rfl
    rw [e, h2]
    exact hN _ hlN
  have hτQ : ∀ x ∈ Q, τ' * x * τ'⁻¹ ∈ Q := (hc.conj_mem_Q_of_mem_M hτ'M).1
  have hdvd := card_conj_free_dvd (D.Q_le_pre N) hτL hτQ
    (fun i hi hio l hl hcomm => hfree i hi (hord ▸ hio) l (D.pre_le N hl) hcomm)
  rw [hord, hcard] at hdvd
  obtain ⟨r, -, hr, -⟩ := hc.hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hodd : Odd (Nat.card Z - 1) := by
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hr
      omega
    have h2 : Even (Nat.card Z) := by
      rw [hr]
      exact Nat.even_pow.mpr ⟨even_two, hr0⟩
    obtain ⟨c, hc'⟩ := h2
    exact ⟨c - 1, by omega⟩
  have hQ : Nat.card Q = Nat.card Z ^ 5 := hw
  have hcop : Nat.Coprime (Nat.card Z - 1) (Nat.card Q) := by
    have h1 : Nat.Coprime (Nat.card Z - 1) (Nat.card Z) := by
      rw [hr]
      exact (Nat.coprime_two_right.mpr (by rwa [← hr])).pow_right r
    rw [hQ]
    exact h1.pow_right 5
  haveI : Finite (M₀.E ≃ₗ[K] M₀.E) := finite_linearEquiv_model M₀
  have hpos : 0 < Nat.card ↥(N ⊓ D.img (LB M Q B)) := Nat.card_pos
  have e2 : Nat.card Q * Nat.card ↥(N ⊓ D.img (LB M Q B)) - Nat.card Q =
      Nat.card Q * (Nat.card ↥(N ⊓ D.img (LB M Q B)) - 1) := by
    rw [Nat.mul_sub_one]
  rw [e2] at hdvd
  exact hcop.dvd_of_dvd_mul_left hdvd

end ActionData

namespace ActionData

variable {hc : Ctx M Q Z B} (D : ActionData hc M₀)

theorem card_img_LB (hL : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z) :
    Nat.card (D.img (LB M Q B)) = Nat.card Z := by
  have h := D.card_img sec39_Q_le_LB hc.LB_le_H0'
  rw [hL] at h
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h).symm

theorem card_le_two_mul_of_cover {Γ : Type*} [Group Γ] [Finite Γ] {J Λ : Subgroup Γ} {t₀ : Γ}
    (hidx : ∀ T ∈ Λ, T ∈ J ∨ T * t₀ ∈ J) : Nat.card Λ ≤ 2 * Nat.card ↥(J ⊓ Λ) := by
  classical
  by_cases hall : ∀ T ∈ Λ, T ∈ J
  · have : J ⊓ Λ = Λ := le_antisymm inf_le_right (fun T hT => ⟨hall T hT, hT⟩)
    rw [this]
    have := Nat.card_pos (α := ↥Λ)
    omega
  · push Not at hall
    obtain ⟨T₀, hT₀Λ, hT₀J⟩ := hall
    have hT₀t : T₀ * t₀ ∈ J := (hidx T₀ hT₀Λ).resolve_left hT₀J
    let f : ↥Λ → ↥(J ⊓ Λ) ⊕ ↥(J ⊓ Λ) := fun T =>
      if h : (T : Γ) ∈ J then Sum.inl ⟨T, h, T.2⟩ else
        Sum.inr ⟨(T : Γ) * T₀⁻¹, by
          have hT := (hidx T T.2).resolve_left h
          have e : (T : Γ) * T₀⁻¹ = ((T : Γ) * t₀) * (T₀ * t₀)⁻¹ := by group
          have hmemJ : (T : Γ) * T₀⁻¹ ∈ J := by
            rw [e]
            exact J.mul_mem hT (J.inv_mem hT₀t)
          exact ⟨hmemJ, Λ.mul_mem T.2 (Λ.inv_mem hT₀Λ)⟩⟩
    have hinj : Function.Injective f := by
      intro a b hab
      by_cases ha : (a : Γ) ∈ J <;> by_cases hb : (b : Γ) ∈ J
      · simp only [f, ha, hb, dif_pos, Sum.inl.injEq] at hab
        have h1 : (a : Γ) = (b : Γ) := congrArg (fun x : ↥(J ⊓ Λ) => (x : Γ)) hab
        exact Subtype.ext h1
      · simp [f, ha, hb] at hab
      · simp [f, ha, hb] at hab
      · simp only [f, ha, hb, dif_neg, not_false_eq_true, Sum.inr.injEq] at hab
        have h1 : (a : Γ) * T₀⁻¹ = (b : Γ) * T₀⁻¹ :=
          congrArg (fun x : ↥(J ⊓ Λ) => (x : Γ)) hab
        exact Subtype.ext (mul_right_cancel h1)
    have := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_sum] at this
    omega

theorem img_LB_le (hw : Width Q Z 2) (hL : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z)
    {τ : G} (hτM : τ ∈ M) (hord : orderOf τ = Nat.card Z - 1)
    (hτL : ∀ l ∈ LB M Q B, τ * l * τ⁻¹ ∈ LB M Q B)
    (hfree : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ l ∈ LB M Q B,
      τ ^ i * l * (τ ^ i)⁻¹ * l⁻¹ ∈ Q → l ∈ Q)
    (J : Subgroup (M₀.E ≃ₗ[K] M₀.E)) (hJ : ∀ g ∈ J, D.C ⟨τ, hτM⟩ g ∈ J)
    {t₀ : M₀.E ≃ₗ[K] M₀.E} (hidx : ∀ T ∈ D.img (LB M Q B), T ∈ J ∨ T * t₀ ∈ J) :
    D.img (LB M Q B) ≤ J := by
  classical
  haveI : Finite (M₀.E ≃ₗ[K] M₀.E) := finite_linearEquiv_model M₀
  have hdvd := D.card_inf_img_dvd hw hτM hord hτL hfree J hJ
  have hcard := D.card_img_LB hL
  have h2 := card_le_two_mul_of_cover (J := J) (Λ := D.img (LB M Q B)) hidx
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hle : Nat.card ↥(J ⊓ D.img (LB M Q B)) ≤ Nat.card Z := by
    rw [← hcard]
    exact Subgroup.card_le_of_le inf_le_right
  have hpos : 0 < Nat.card ↥(J ⊓ D.img (LB M Q B)) := Nat.card_pos
  have hge : Nat.card Z ≤ Nat.card ↥(J ⊓ D.img (LB M Q B)) := by
    obtain ⟨c, hc'⟩ := hdvd
    rw [hcard] at h2
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0
      omega
    · have h3 : (Nat.card Z - 1) * 1 ≤ (Nat.card Z - 1) * c := Nat.mul_le_mul_left _ h0
      omega
  have hEq : Nat.card ↥(J ⊓ D.img (LB M Q B)) = Nat.card Z := le_antisymm hle hge
  have hEq' : J ⊓ D.img (LB M Q B) = D.img (LB M Q B) :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hEq, hcard])
  exact hEq' ▸ inf_le_left

end ActionData

namespace ActionData

variable {hc : Ctx M Q Z B} (D : ActionData hc M₀)

theorem inf_img_eq_bot_or_eq (hw : Width Q Z 2)
    (hL : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z) {τ : G} (hτM : τ ∈ M)
    (hord : orderOf τ = Nat.card Z - 1)
    (hτL : ∀ l ∈ LB M Q B, τ * l * τ⁻¹ ∈ LB M Q B)
    (hfree : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ l ∈ LB M Q B,
      τ ^ i * l * (τ ^ i)⁻¹ * l⁻¹ ∈ Q → l ∈ Q)
    (N : Subgroup (M₀.E ≃ₗ[K] M₀.E))
    (hN : ∀ g ∈ N, D.C ⟨τ * τ, M.mul_mem hτM hτM⟩ g ∈ N) :
    N ⊓ D.img (LB M Q B) = ⊥ ∨ N ⊓ D.img (LB M Q B) = D.img (LB M Q B) := by
  classical
  haveI : Finite (M₀.E ≃ₗ[K] M₀.E) := finite_linearEquiv_model M₀
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨r, -, hr, -⟩ := hc.hyp.cp
  have hodd : Odd (Nat.card Z - 1) := by
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hr
      omega
    have h2 : Even (Nat.card Z) := by
      rw [hr]
      exact Nat.even_pow.mpr ⟨even_two, hr0⟩
    obtain ⟨c, hc'⟩ := h2
    exact ⟨c - 1, by omega⟩
  have hcop2 : Nat.Coprime (Nat.card Z - 1) 2 := Nat.coprime_two_right.mpr hodd
  have hord' : orderOf (τ * τ) = Nat.card Z - 1 := by
    have h1 : orderOf (τ ^ 2) = orderOf τ := Nat.Coprime.orderOf_pow (by rw [hord]; exact hcop2)
    rw [← sq, h1, hord]
  have hτ'L : ∀ l ∈ LB M Q B, τ * τ * l * (τ * τ)⁻¹ ∈ LB M Q B := by
    intro l hl
    have e : τ * τ * l * (τ * τ)⁻¹ = τ * (τ * l * τ⁻¹) * τ⁻¹ := by group
    rw [e]
    exact hτL _ (hτL l hl)
  have hfree' : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ l ∈ LB M Q B,
      (τ * τ) ^ i * l * ((τ * τ) ^ i)⁻¹ * l⁻¹ ∈ Q → l ∈ Q := by
    intro i hi hio l hl hcomm
    have e : τ ^ (2 * i % orderOf τ) = (τ * τ) ^ i := by
      rw [pow_mod_orderOf, ← sq, ← pow_mul]
    rw [hord] at e
    have hj0 : 0 < 2 * i % (Nat.card Z - 1) := by
      rcases Nat.eq_zero_or_pos (2 * i % (Nat.card Z - 1)) with h0 | h0
      · exfalso
        have hdvd : Nat.card Z - 1 ∣ 2 * i := Nat.dvd_of_mod_eq_zero h0
        have hdvd' : Nat.card Z - 1 ∣ i := hcop2.dvd_of_dvd_mul_left hdvd
        have := Nat.le_of_dvd hi hdvd'
        omega
      · exact h0
    have hjlt : 2 * i % (Nat.card Z - 1) < Nat.card Z - 1 := Nat.mod_lt _ (by omega)
    refine hfree _ hj0 hjlt l hl ?_
    rw [e]
    exact hcomm
  have hdvd := D.card_inf_img_dvd hw (M.mul_mem hτM hτM) hord' hτ'L hfree' N hN
  have hcard := D.card_img_LB hL
  have hle : Nat.card ↥(N ⊓ D.img (LB M Q B)) ≤ Nat.card Z := by
    rw [← hcard]
    exact Subgroup.card_le_of_le inf_le_right
  have hpos : 0 < Nat.card ↥(N ⊓ D.img (LB M Q B)) := Nat.card_pos
  obtain ⟨c, hc'⟩ := hdvd
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · left
    subst h0
    refine Subgroup.eq_bot_of_card_eq _ ?_
    omega
  · right
    have h3 : (Nat.card Z - 1) * 1 ≤ (Nat.card Z - 1) * c := Nat.mul_le_mul_left _ h0
    have hEq : Nat.card ↥(N ⊓ D.img (LB M Q B)) = Nat.card Z := by omega
    exact Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hEq, hcard])

end ActionData

namespace ActionData

variable {hc : Ctx M Q Z B} (D : ActionData hc M₀)

theorem Lgen_le_H0 (hc : Ctx M Q Z B) : Lgen M (LB M Q B) ≤ H0 M Z := by
  refine iSup₂_le fun m hm x hx => ?_
  rw [mem_conjSubgroup] at hx
  have h1 : (m : G)⁻¹ * x * m ∈ H0 M Z := hc.LB_le_H0' hx
  have h2 := hc.conj_mem_H0 hm h1
  have e : (m : G) * ((m : G)⁻¹ * x * (m : G)) * (m : G)⁻¹ = x := by group
  rwa [e] at h2

theorem eq_bot_of_normal_pGroup (R : Subgroup (M₀.E ≃ₗ[K] M₀.E))
    (hRS : R ≤ D.img (Lgen M (LB M Q B)))
    (hRn : ∀ s ∈ D.img (Lgen M (LB M Q B)), ∀ r ∈ R, s * r * s⁻¹ ∈ R)
    (hR2 : IsPGroup 2 ↥R) : R = ⊥ := by
  classical
  set Lg := Lgen M (LB M Q B) with hLg
  set S := D.img Lg with hS
  have hLgH0 : Lg ≤ H0 M Z := Lgen_le_H0 hc
  have hLgM : Lg ≤ M := Lgen_le hc.LB_le_M
  have hLgn : ∀ m ∈ M, conjSubgroup m Lg = Lg := fun m hm =>
    conjSubgroup_eq_self_iff.mpr (Lgen_normalizes M _ hm)
  have hSinv : ∀ m : ↥M, S.map (D.C m).toMonoidHom = S := by
    intro m
    rw [hS, ← D.img_conj hLgH0 m, hLgn m m.2]
  set R₀ : Subgroup (M₀.E ≃ₗ[K] M₀.E) := inSubgroup (pCore 2) S with hR₀
  have hSnorm : S ≤ Subgroup.normalizer (R : Set (M₀.E ≃ₗ[K] M₀.E)) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      exact hRn s hs r hr
    · intro hr
      have := hRn s⁻¹ (S.inv_mem hs) _ hr
      simpa [mul_assoc] using this
  have hRR₀ : R ≤ R₀ := Tim78.le_inSubgroup_pCore hRS hSnorm hR2
  have hR₀2 : IsPGroup 2 ↥R₀ := by
    have h := (CFSG.pCore_isPGroup (p := 2) (G := ↥S)).map S.subtype
    exact h
  have hR₀S : R₀ ≤ S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hR₀inv : ∀ m : ↥M, R₀.map (D.C m).toMonoidHom = R₀ := by
    intro m
    have hpc : R₀.map (D.C m).toMonoidHom =
        inSubgroup (pCore 2) (S.map (D.C m).toMonoidHom) := by
      rw [hR₀, inSubgroup, inSubgroup,
        ← CFSG.pCore_map_iso 2 (S.equivMapOfInjective (D.C m).toMonoidHom (D.C m).injective),
        Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [hpc, hSinv m]
  let ΨL : ↥Lg →* (M₀.E ≃ₗ[K] M₀.E) := D.Ψ.comp (Subgroup.inclusion hLgH0)
  have hQ2 : IsPGroup 2 ↥Q := by
    rw [hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  have hker2 : IsPGroup 2 ↥ΨL.ker := by
    have hkerle : ΨL.ker = Q.subgroupOf Lg := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact D.hΨker (Subgroup.inclusion hLgH0 x)
    rw [hkerle]
    exact hQ2.comap_of_injective Lg.subtype Lg.subtype_injective
  set Ř : Subgroup G := (R₀.comap ΨL).map Lg.subtype with hŘ
  have hŘmem : ∀ x : G, x ∈ Ř ↔ ∃ hx : x ∈ Lg, ΨL ⟨x, hx⟩ ∈ R₀ := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hΨ⟩
      exact ⟨⟨x, hx⟩, hΨ, rfl⟩
  have hŘM : Ř ≤ M := fun x hx => hLgM ((hŘmem x).mp hx).1
  have hŘ2 : IsPGroup 2 ↥Ř := (hR₀2.comap_of_ker_isPGroup ΨL hker2).map Lg.subtype
  have hŘn : M ≤ Subgroup.normalizer (Ř : Set G) := by
    have hconj : ∀ m ∈ M, ∀ x ∈ Ř, m * x * m⁻¹ ∈ Ř := by
      intro m hm x hx
      obtain ⟨hxL, hxΨ⟩ := (hŘmem x).mp hx
      have hmx : m * x * m⁻¹ ∈ Lg := by
        have : m * x * m⁻¹ ∈ conjSubgroup m Lg := by
          rw [mem_conjSubgroup]
          have e : m⁻¹ * (m * x * m⁻¹) * m = x := by group
          rw [e]
          exact hxL
        rwa [hLgn m hm] at this
      refine (hŘmem _).mpr ⟨hmx, ?_⟩
      have h1 := D.hΨC ⟨m, hm⟩ (Subgroup.inclusion hLgH0 ⟨x, hxL⟩)
      have e : ΨL ⟨m * x * m⁻¹, hmx⟩ =
          D.Ψ ⟨(m : G) * ((Subgroup.inclusion hLgH0 ⟨x, hxL⟩ : ↥(H0 M Z)) : G) * (m : G)⁻¹,
            hc.conj_mem_H0 hm (Subgroup.inclusion hLgH0 ⟨x, hxL⟩).2⟩ := rfl
      rw [e, h1]
      have : D.C ⟨m, hm⟩ (ΨL ⟨x, hxL⟩) ∈ R₀.map (D.C ⟨m, hm⟩).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hxΨ
      rwa [hR₀inv ⟨m, hm⟩] at this
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hconj m hm x hx, fun hx => by
      have := hconj m⁻¹ (M.inv_mem hm) _ hx
      simpa [mul_assoc] using this⟩
  have hŘQ : Ř ≤ Q := by
    have := Tim78.le_inSubgroup_pCore hŘM hŘn hŘ2
    rwa [← hc.hyp.hQ] at this
  have hR₀bot : R₀ = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun r hr => ?_
    obtain ⟨l, hlL, rfl⟩ := D.mem_img.mp (hR₀S hr)
    have hlŘ : (l : G) ∈ Ř := (hŘmem _).mpr ⟨hlL, hr⟩
    exact (D.hΨker l).mpr (hŘQ hlŘ)
  exact le_bot_iff.mp (hR₀bot ▸ hRR₀)

end ActionData

namespace ActionData

variable {hc : Ctx M Q Z B} (D : ActionData hc M₀)

theorem not_omega_le_img (hw : Width Q Z 2) (h : GlobalModelData M Q Z γ M₀)
    (hJ : ⁅orthogonalGroup M₀.toQuadraticForm, orthogonalGroup M₀.toQuadraticForm⁆ ≤
      D.img (Lgen M (LB M Q B))) : False := by
  refine BeisiegelSatz5Stroth hc.hyp h hw (le_refl 2) (Lgen_le_H0 hc) ?_
  intro T hT
  obtain ⟨l, hl, rfl⟩ := D.mem_img.mp (hJ hT)
  exact ⟨(l : G), hl, fun x hx => D.hΨπ l x hx⟩

theorem img_Lgen_eq_iSup :
    D.img (Lgen M (LB M Q B)) = ⨆ m : ↥M, (D.img (LB M Q B)).map (D.C m).toMonoidHom := by
  have hLgH0 : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  apply le_antisymm
  ·
    set T : Subgroup (M₀.E ≃ₗ[K] M₀.E) :=
      ⨆ m : ↥M, (D.img (LB M Q B)).map (D.C m).toMonoidHom with hT
    set P : Subgroup G := (T.comap D.Ψ).map (H0 M Z).subtype with hP
    have hLP : Lgen M (LB M Q B) ≤ P := by
      refine iSup₂_le fun m hm x hx => ?_
      have hxH : x ∈ H0 M Z := by
        rw [mem_conjSubgroup] at hx
        have h1 : (m : G)⁻¹ * x * m ∈ H0 M Z := hc.LB_le_H0' hx
        have h2 := hc.conj_mem_H0 hm h1
        have e : (m : G) * ((m : G)⁻¹ * x * (m : G)) * (m : G)⁻¹ = x := by group
        rwa [e] at h2
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      show D.Ψ ⟨x, hxH⟩ ∈ T
      have hmem : D.Ψ ⟨x, hxH⟩ ∈ D.img (conjSubgroup m (LB M Q B)) :=
        D.mem_img.mpr ⟨⟨x, hxH⟩, hx, rfl⟩
      rw [D.img_conj hc.LB_le_H0' ⟨m, hm⟩] at hmem
      exact Subgroup.mem_iSup_of_mem (⟨m, hm⟩ : ↥M) hmem
    intro g hg
    obtain ⟨l, hl, rfl⟩ := D.mem_img.mp hg
    obtain ⟨l', hl', hl'e⟩ := hLP hl
    have : l' = l := Subtype.ext hl'e
    rw [← this]
    exact hl'
  · refine iSup_le fun m => ?_
    rw [← D.img_conj hc.LB_le_H0' m]
    refine D.img_mono ?_
    show conjSubgroup (m : G) (LB M Q B) ≤ Lgen M (LB M Q B)
    unfold Lgen
    exact le_iSup₂_of_le (m : G) m.2 le_rfl

end ActionData

namespace ActionData

variable {hc : Ctx M Q Z B} (D : ActionData hc M₀)

theorem sl2_core (hw : Width Q Z 2) (h : GlobalModelData M Q Z γ M₀)
    (hL : Nat.card (LB M Q B) = Nat.card Q * Nat.card Z)
    {τ : G} (hτM : τ ∈ M) (hord : orderOf τ = Nat.card Z - 1)
    (hτL : ∀ l ∈ LB M Q B, τ * l * τ⁻¹ ∈ LB M Q B)
    (hfree : ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ l ∈ LB M Q B,
      τ ^ i * l * (τ ^ i)⁻¹ * l⁻¹ ∈ Q → l ∈ Q) :
    Nonempty (↥(D.img (Lgen M (LB M Q B))) ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  haveI : Module.Finite K M₀.E := M₀.fin
  haveI : Finite (M₀.E ≃ₗ[K] M₀.E) := finite_linearEquiv_model M₀
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hKcard : Nat.card K = Nat.card Z := h.card
  have h4 : 4 ≤ Nat.card K := by omega
  have hK1 : 1 < Nat.card K := by omega
  have hdim : Module.finrank K M₀.E = 4 := h.finrank_E hw hK1
  have hnd := polarBilin_toQuadraticForm_nondegenerate M₀
  obtain ⟨S₁, S₂, hS12, hS₁, hS₂⟩ := h.hyperbolic
  have hS1dim : Module.finrank K S₁ = 2 := by
    have h1 := Tim79.QuadModel.two_mul_finrank_le_of_totallySingular M₀ S₁ hS₁
    have h2 := Tim79.QuadModel.two_mul_finrank_le_of_totallySingular M₀ S₂ hS₂
    have h3 := Submodule.finrank_add_eq_of_isCompl hS12
    omega
  obtain ⟨ρ, hρinj, hρrange, -, t₀, -, hidx⟩ :=
    SL2Coord.exists_omega_equiv M₀.toQuadraticForm hnd hdim S₁ hS1dim hS₁ h4
  have hφ : ∀ (m : ↥M) z, D.C m (ρ z) ∈ ρ.range := by
    intro m z
    have h1 : ρ z ∈ ⁅orthogonalGroup M₀.toQuadraticForm, orthogonalGroup M₀.toQuadraticForm⁆ := by
      rw [← hρrange]
      exact ⟨z, rfl⟩
    have h2 := Subgroup.mem_map_of_mem (D.C m).toMonoidHom h1
    rw [D.hCJ m, ← hρrange] at h2
    exact h2
  have hφ' : ∀ (m : ↥M) z, (D.C m).symm (ρ z) ∈ ρ.range := by
    intro m z
    have h1 : ρ z ∈ ⁅orthogonalGroup M₀.toQuadraticForm, orthogonalGroup M₀.toQuadraticForm⁆ := by
      rw [← hρrange]
      exact ⟨z, rfl⟩
    rw [← D.hCJ m] at h1
    obtain ⟨y, hy, hyz⟩ := h1
    have : (D.C m).symm (ρ z) = y := by
      rw [← hyz]
      exact (D.C m).symm_apply_apply y
    rw [this, ← hρrange] at *
    exact hy
  have hΛO : ∀ T ∈ D.img (LB M Q B), T ∈ orthogonalGroup M₀.toQuadraticForm := by
    intro T hT
    obtain ⟨l, hl, rfl⟩ := D.mem_img.mp hT
    rw [mem_orthogonalGroup_iff]
    exact fun e => D.hΨiso l e
  have hΛJ : D.img (LB M Q B) ≤ ρ.range :=
    D.img_LB_le hw hL hτM hord hτL hfree ρ.range (fun g hg => by
      obtain ⟨z, rfl⟩ := hg
      exact hφ ⟨τ, hτM⟩ z) (fun T hT => hidx T (hΛO T hT))
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := SL2Grp.sl2_isSimpleGroup h4
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) K) := SL2Grp.sl2_finite K
  have hX := SL2Grp.sl2_nonabelian (K := K)
  have hnot := SL2Grp.sl2_not_isPGroup h4
  have hgen : ∀ P P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K), IsPGroup 2 ↥P →
      IsPGroup 2 ↥P' → Nat.card ↥P = Nat.card K → Nat.card ↥P' = Nat.card K → P ≠ P' →
      P ⊔ P' = ⊤ := fun P P' _ _ hcP hcP' hne =>
    SL2Grp.two_sylow_generate hcP hcP' hne
  set Λ := D.img (LB M Q B) with hΛ
  set Λ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :=
    Λ.comap ρ with hΛ'
  have hmapΛ' : Λ'.map ρ = Λ := Subgroup.map_comap_eq_self hΛJ
  have hQ2 : IsPGroup 2 ↥Q := by
    rw [hc.hyp.hQ]
    exact (inSubgroup_pCore_two M).1
  have hLB2 : IsPGroup 2 ↥(LB M Q B) := by
    intro l
    have h2 : (l : G) ^ 2 ∈ Q := hc.sq_mem_Q_of_mem_LB l.2
    obtain ⟨k, hk⟩ := hQ2 ⟨_, h2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_succ', pow_mul]
    exact this
  have hΛ2 : IsPGroup 2 ↥Λ := D.isPGroup_img hc.LB_le_H0' hLB2
  have hΛ'2 : IsPGroup 2 ↥Λ' := hΛ2.comap_of_injective ρ hρinj
  have hΛ'card : Nat.card ↥Λ' = Nat.card K := by
    have h1 : Nat.card (Λ'.map ρ) = Nat.card Λ' := Subgroup.card_map_of_injective hρinj
    rw [hmapΛ'] at h1
    rw [← h1, D.card_img_LB hL, hKcard]
  have hperm := SL2Grp.perm_of_stable hX ρ hρinj (D.C ⟨τ, hτM⟩) (hφ _) (hφ' _)
  have hsq := SL2Grp.perm_sq hperm
  have hττ : ∀ g, D.C (⟨τ, hτM⟩ * ⟨τ, hτM⟩) g = D.C ⟨τ, hτM⟩ (D.C ⟨τ, hτM⟩ g) :=
    fun g => D.hCmul _ _ g
  have hN : ∀ N : Subgroup (M₀.E ≃ₗ[K] M₀.E),
      (N.map (D.C ⟨τ, hτM⟩).toMonoidHom).map (D.C ⟨τ, hτM⟩).toMonoidHom = N →
      ∀ g ∈ N, D.C ⟨τ * τ, M.mul_mem hτM hτM⟩ g ∈ N := by
    intro N hNN g hg
    have h1 : D.C ⟨τ, hτM⟩ g ∈ N.map (D.C ⟨τ, hτM⟩).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hg
    have h2 : D.C ⟨τ, hτM⟩ (D.C ⟨τ, hτM⟩ g) ∈
        (N.map (D.C ⟨τ, hτM⟩).toMonoidHom).map (D.C ⟨τ, hτM⟩).toMonoidHom :=
      Subgroup.mem_map_of_mem _ h1
    rw [hNN] at h2
    have h3 := hττ g
    exact h3 ▸ h2
  have hbot₁ := D.inf_img_eq_bot_or_eq hw hL hτM hord hτL hfree ((SL2Grp.fac₁ _).map ρ)
    (hN _ hsq.1)
  have hbot₂ := D.inf_img_eq_bot_or_eq hw hL hτM hord hτL hfree ((SL2Grp.fac₂ _).map ρ)
    (hN _ hsq.2)
  have hcomap : ∀ F : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K), ((F.map ρ).comap ρ) = F :=
    fun F => Subgroup.comap_map_eq_self_of_injective hρinj F
  have hkerbot : (⊥ : Subgroup (M₀.E ≃ₗ[K] M₀.E)).comap ρ = ⊥ := by
    rw [MonoidHom.comap_bot]
    exact (MonoidHom.ker_eq_bot_iff ρ).mpr hρinj
  have hTri : SL2Grp.Tri Λ' := by
    rcases hbot₁ with h1 | h1
    · rcases hbot₂ with h2 | h2
      · right
        right
        constructor
        · have : Λ' ⊓ SL2Grp.fac₁ _ = (((SL2Grp.fac₁ _).map ρ) ⊓ Λ).comap ρ := by
            rw [Subgroup.comap_inf, hcomap, inf_comm]
          rw [this, h1, hkerbot]
        · have : Λ' ⊓ SL2Grp.fac₂ _ = (((SL2Grp.fac₂ _).map ρ) ⊓ Λ).comap ρ := by
            rw [Subgroup.comap_inf, hcomap, inf_comm]
          rw [this, h2, hkerbot]
      · right
        left
        have hle : Λ ≤ (SL2Grp.fac₂ _).map ρ := inf_eq_right.mp h2
        calc Λ' ≤ ((SL2Grp.fac₂ _).map ρ).comap ρ := Subgroup.comap_mono hle
          _ = SL2Grp.fac₂ _ := hcomap _
    · left
      have hle : Λ ≤ (SL2Grp.fac₁ _).map ρ := inf_eq_right.mp h1
      calc Λ' ≤ ((SL2Grp.fac₁ _).map ρ).comap ρ := Subgroup.comap_mono hle
        _ = SL2Grp.fac₁ _ := hcomap _
  choose α hα using fun m : ↥M =>
    SL2Grp.exists_aut_of_stable ρ hρinj (D.C m) (hφ m) (hφ' m)
  set S' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :=
    ⨆ m : ↥M, Λ'.map (α m).toMonoidHom with hS'
  have hρS' : S'.map ρ = D.img (Lgen M (LB M Q B)) := by
    rw [D.img_Lgen_eq_iSup, hS', Subgroup.map_iSup]
    refine iSup_congr fun m => ?_
    rw [Subgroup.map_map]
    have hcomp : ρ.comp (α m).toMonoidHom = (D.C m).toMonoidHom.comp ρ :=
      MonoidHom.ext fun z => hα m z
    rw [hcomp, ← Subgroup.map_map, hmapΛ']
  have hO2 : ∀ R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K), R ≤ S' → (∀ s ∈ S', ∀ r ∈ R, s * r * s⁻¹ ∈ R) →
      IsPGroup 2 ↥R → R = ⊥ := by
    intro R hRS hRn hR2
    have h1 : R.map ρ ≤ D.img (Lgen M (LB M Q B)) := by
      rw [← hρS']
      exact Subgroup.map_mono hRS
    have h2 : ∀ s ∈ D.img (Lgen M (LB M Q B)), ∀ r ∈ R.map ρ, s * r * s⁻¹ ∈ R.map ρ := by
      intro s hs r hr
      rw [← hρS'] at hs
      obtain ⟨s', hs', rfl⟩ := hs
      obtain ⟨r', hr', rfl⟩ := hr
      exact ⟨s' * r' * s'⁻¹, hRn s' hs' r' hr', by simp⟩
    have h3 : IsPGroup 2 ↥(R.map ρ) := hR2.map ρ
    have h4' := D.eq_bot_of_normal_pGroup (R.map ρ) h1 h2 h3
    exact (Subgroup.map_eq_bot_iff_of_injective R (f := ρ) hρinj).mp h4'
  have htop : S' ≠ ⊤ := by
    intro hS
    apply D.not_omega_le_img hw h
    rw [← hρS', hS, ← MonoidHom.range_eq_map, hρrange]
  have hS'eq : S' = ⨆ α' ∈ Set.range α, Λ'.map α'.toMonoidHom := by
    rw [hS']
    exact (iSup_range (g := fun α' : (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) ≃* (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) => Λ'.map α'.toMonoidHom) (f := α)).symm
  obtain ⟨e⟩ := SL2Grp.exists_mulEquiv_of_conj_family hX (q := Nat.card K) (by omega) hnot hgen
    hΛ'2 hΛ'card hTri (Set.range α) (Set.range_nonempty α) hS'eq hO2 htop
  have e2 : ↥S' ≃* ↥(S'.map ρ) := Subgroup.equivMapOfInjective S' ρ hρinj
  have e3 : ↥(S'.map ρ) ≃* ↥(D.img (Lgen M (LB M Q B))) := MulEquiv.subgroupCongr hρS'
  exact ⟨(e2.trans e3).symm.trans e⟩

end ActionData

theorem stroth123SL2_holds : Stroth123SL2Statement := by
  classical
  intro G _ _ M Q Z B hc hw hL
  obtain ⟨K, _, _, hchar, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  haveI := hchar
  obtain ⟨D⟩ := exists_actionData hc h
  obtain ⟨τ, hτM, hord, hτL, hfree⟩ := stroth123Fpf_holds G M Q Z B hc hw
  obtain ⟨e⟩ := D.sl2_core hw h hL hτM hord hτL hfree
  have hLgH0 : Lgen M (LB M Q B) ≤ H0 M Z := ActionData.Lgen_le_H0 hc
  have hLgM : Lgen M (LB M Q B) ≤ M := Lgen_le hc.LB_le_M
  have hQLg : Q ≤ Lgen M (LB M Q B) := sec39_Q_le_LB.trans (le_Lgen_self M _)
  have hnorm : (Q.subgroupOf (Lgen M (LB M Q B))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQLg]
    exact fun x hx => hc.hyp.Q_normal.2 (hLgM hx)
  refine ⟨hnorm, ?_⟩
  let ΨL : ↥(Lgen M (LB M Q B)) →* (M₀.E ≃ₗ[K] M₀.E) :=
    D.Ψ.comp (Subgroup.inclusion hLgH0)
  have hkerΨL : ΨL.ker = Q.subgroupOf (Lgen M (LB M Q B)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact D.hΨker (Subgroup.inclusion hLgH0 x)
  have hrange : ΨL.range = D.img (Lgen M (LB M Q B)) := D.range_eq_img hLgH0
  let e1 : (↥(Lgen M (LB M Q B)) ⧸ Q.subgroupOf (Lgen M (LB M Q B))) ≃* ΨL.range :=
    (QuotientGroup.quotientMulEquivOfEq hkerΨL.symm).trans (QuotientGroup.quotientKerEquivRange ΨL)
  let e2 : ΨL.range ≃* ↥(D.img (Lgen M (LB M Q B))) := MulEquiv.subgroupCongr hrange
  exact ⟨K, inferInstance, inferInstance, h.card,
    ⟨((e1.trans e2).trans e).trans (specialLinearGroupEquivStatedSL 2 K)⟩⟩

theorem stroth123Statement_holds : Stroth123Statement :=
  stroth123_of_fpf_sl2 stroth123Fpf_holds stroth123SL2_holds

end CFSG.RankThree.GF2n.Stroth80
