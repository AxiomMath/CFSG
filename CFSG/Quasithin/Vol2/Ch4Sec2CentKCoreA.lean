module

public import CFSG.Quasithin.Background.A4V
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKDefs

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank Matrix
open CFSG.Open hiding StatedSL
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure CoreHyp (R Rp H K Q LH V : Subgroup G) (F : Type) [Field F] [Fintype F]
    (α : ↥K →* ↥(StatedSL 3 F)) (β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)) : Prop where
  Rp2 : IsPGroup 2 Rp
  RRp : R ≤ Rp
  RpH : Rp ⊓ H ≤ R
  VΩ : V ≤ omegaOneCenterOf R
  VRp : Rp ≤ Subgroup.centralizer (V : Set G)
  ΩQ : omegaOneCenterOf R ⊓ Q ≤ V
  ΩK : ⁅omegaOneCenterOf R, K⁆ ≤ Q
  LHK : LH ≤ K
  LHp : ⁅LH, LH⁆ = LH
  LHR : LH ≤ Subgroup.normalizer (R : Set G)
  LHRp : LH ≤ Subgroup.normalizer (Rp : Set G)
  RLH : R ≤ Subgroup.normalizer (LH : Set G)
  LHV : LH ≤ Subgroup.normalizer (V : Set G)
  LH_C : omegaOneCenterOf R ⊓ Subgroup.centralizer (LH : Set G) ≤
    Subgroup.centralizer (K : Set G)
  CV : ∀ v ∈ V, (∀ t ∈ LH, t * t ∈ R → t * v = v * t) → v = 1
  NQ : Subgroup.normalizer (Q : Set G) ≤ H
  NZ : omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥ →
    Subgroup.normalizer ((omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :
      Set G) ≤ H
  RZ : R = Rp → omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) = ⊥
  h27 : ∀ Y : Subgroup G, Y ≤ H → ⁅Y, Y⁆ = Y →
    (∃ ρ : ↥Y →* ↥(StatedSL 2 F), Function.Surjective ρ ∧ IsPGroup 2 ρ.ker) → Y ≤ K
  co : CoordData K Q F α β
  αsurj : Function.Surjective α
  αker : α.ker = CFSG.pCore 2 ↥K
  F2 : ∃ m : ℕ, 2 ≤ m ∧ Fintype.card F = 2 ^ m
  VS : VStruct K Q V F α

private theorem coreA_conj_eq {V : Subgroup G} {g v : G}
    (hg : g ∈ Subgroup.centralizer (V : Set G)) (hv : v ∈ V) : g * v * g⁻¹ = v := by
  have h1 : v * g = g * v := Subgroup.mem_centralizer_iff.mp hg v hv
  rw [← h1, mul_inv_cancel_right]

private theorem coreA_conj_E {V : Subgroup G} {g x y : G}
    (hg : g ∈ Subgroup.centralizer (V : Set G)) (hxy : x * y⁻¹ ∈ V) :
    (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ ∈ V := by
  have e : (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (x * y⁻¹) * g⁻¹ := by group
  rw [e, coreA_conj_eq hg hxy]
  exact hxy

private theorem coreA_conj_omega {R : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) (hx : x ∈ omegaOneCenterOf R) :
    g * x * g⁻¹ ∈ omegaOneCenterOf R :=
  (Subgroup.mem_normalizer_iff.mp
    (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf R hg) x).mp hx

private theorem coreA_conj_omega_inv {R : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) (hx : x ∈ omegaOneCenterOf R) :
    g⁻¹ * x * g ∈ omegaOneCenterOf R := by
  have := coreA_conj_omega (Subgroup.inv_mem _ hg) hx
  rwa [inv_inv] at this

private theorem coreA_normalizer_centralizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ c ∈ Subgroup.centralizer (X : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    have h1 := hc _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact key g hg c hc
  · intro hc
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
    simpa [mul_assoc] using this

private theorem mem_sup_coreA {W N : Subgroup G} (hWN : W ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ W ⊔ N) : ∃ w ∈ W, ∃ n ∈ N, w * n = x := by
  have hle : W ⊔ N ≤ Subgroup.normalizer (N : Set G) := sup_le hWN Subgroup.le_normalizer
  have hNn : (N.subgroupOf (W ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hle
  have hx' : (⟨x, hx⟩ : ↥(W ⊔ N)) ∈ W.subgroupOf (W ⊔ N) ⊔ N.subgroupOf (W ⊔ N) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨w, hw, n, hn, hwn⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨w, hw, n, hn, congrArg Subtype.val hwn⟩

private theorem map_subgroupOf_sup_eq_top_coreA {W N : Subgroup G}
    (hWN : W ≤ Subgroup.normalizer (N : Set G)) [(N.subgroupOf (W ⊔ N)).Normal] :
    (W.subgroupOf (W ⊔ N)).map (QuotientGroup.mk' (N.subgroupOf (W ⊔ N))) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨w, hw, n, hn, hwn⟩ := mem_sup_coreA hWN u.2
  refine ⟨⟨w, le_sup_left (a := W) hw⟩, hw, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have : (((⟨w, le_sup_left (a := W) hw⟩ : ↥(W ⊔ N))⁻¹ * u : ↥(W ⊔ N)) : G) = n := by
    show w⁻¹ * (u : G) = n
    rw [← hwn]
    group
  rw [this]
  exact hn

private theorem le_of_map_eq_bot_coreA {K W N : Subgroup G} (hKWN : K ≤ W ⊔ N)
    [(N.subgroupOf (W ⊔ N)).Normal]
    (h : (K.subgroupOf (W ⊔ N)).map (QuotientGroup.mk' (N.subgroupOf (W ⊔ N))) = ⊥) :
    K ≤ N := by
  intro x hx
  have h1 : QuotientGroup.mk' (N.subgroupOf (W ⊔ N)) (⟨x, hKWN hx⟩ : ↥(W ⊔ N)) ∈
      (K.subgroupOf (W ⊔ N)).map (QuotientGroup.mk' (N.subgroupOf (W ⊔ N))) :=
    ⟨⟨x, hKWN hx⟩, hx, rfl⟩
  rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem le_of_perfect_of_le_sup_coreA {K W N : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hWN : W ≤ Subgroup.normalizer (N : Set G)) (hW : Group.IsSolvable W)
    (hKWN : K ≤ W ⊔ N) : K ≤ N := by
  have hKp : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
  have hNn : (N.subgroupOf (W ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hWN Subgroup.le_normalizer)
  have htop := map_subgroupOf_sup_eq_top_coreA hWN
  have hsolv : Group.IsSolvable (↥(W ⊔ N) ⧸ N.subgroupOf (W ⊔ N)) := by
    have hWs : Group.IsSolvable (W.subgroupOf (W ⊔ N)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : W ≤ W ⊔ N)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : W ≤ W ⊔ N)).injective
    have hsurj : Function.Surjective
        ((QuotientGroup.mk' (N.subgroupOf (W ⊔ N))).comp (W.subgroupOf (W ⊔ N)).subtype) := by
      intro y
      have hy : y ∈ (W.subgroupOf (W ⊔ N)).map (QuotientGroup.mk' (N.subgroupOf (W ⊔ N))) :=
        htop ▸ Subgroup.mem_top y
      obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨⟨w, hw⟩, rfl⟩
    exact Group.isSolvable_of_surjective hsurj
  have hKU : Group.IsPerfect (K.subgroupOf (W ⊔ N)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKWN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKWN).symm.surjective
  refine le_of_map_eq_bot_coreA hKWN ?_
  by_contra hne
  have : Nontrivial ((K.subgroupOf (W ⊔ N)).map (QuotientGroup.mk' (N.subgroupOf (W ⊔ N)))) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have : Group.IsPerfect ((K.subgroupOf (W ⊔ N)).map (QuotientGroup.mk' (N.subgroupOf (W ⊔ N)))) :=
    Group.IsPerfect.map _
  have : Group.IsSolvable ((K.subgroupOf (W ⊔ N)).map (QuotientGroup.mk' (N.subgroupOf (W ⊔ N)))) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  exact Group.IsPerfect.not_isSolvable _ this

section Steps

variable {R Rp H K Q LH V : Subgroup G} {F : Type} [Field F] [Fintype F]
  {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}

@[expose] def InR2 (R Rp V : Subgroup G) (s : G) : Prop :=
  s ∈ Rp ∧ s ∈ Subgroup.normalizer (R : Set G) ∧ ∀ ω ∈ omegaOneCenterOf R, ⁅ω, s⁆ ∈ V

private theorem coreA_F1 (h : CoreHyp R Rp H K Q LH V F α β) {g x : G} (hg : g ∈ LH)
    (hx : x ∈ omegaOneCenterOf R) : x * (g * x * g⁻¹)⁻¹ ∈ V := by
  have e : x * (g * x * g⁻¹)⁻¹ = ⁅x, g⁆ := by
    simp only [commutatorElement_def]; group
  have hgx : g * x * g⁻¹ ∈ omegaOneCenterOf R := coreA_conj_omega (h.LHR hg) hx
  rw [e]
  refine h.ΩQ (Subgroup.mem_inf.mpr ⟨?_, h.ΩK (Subgroup.commutator_mem_commutator hx (h.LHK hg))⟩)
  rw [← e]
  exact (omegaOneCenterOf R).mul_mem hx ((omegaOneCenterOf R).inv_mem hgx)

private theorem coreA_F1' (h : CoreHyp R Rp H K Q LH V F α β) {g x : G} (hg : g ∈ LH)
    (hx : x ∈ omegaOneCenterOf R) : x * (g⁻¹ * x * g)⁻¹ ∈ V := by
  have := coreA_F1 h (LH.inv_mem hg) hx
  rwa [inv_inv] at this

theorem omega_comm_R {a r : G} (ha : a ∈ omegaOneCenterOf R) (hr : r ∈ R) : a * r = r * a :=
  (Subgroup.mem_centralizer_iff.mp
    (CFSG.Quasithin.A4.centerOf_le_centralizer R
      (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf R ha)) r hr).symm

theorem inR2_mul (h : CoreHyp R Rp H K Q LH V F α β) {s s' : G} (hs : InR2 R Rp V s)
    (hs' : InR2 R Rp V s') : InR2 R Rp V (s * s') := by
  unfold InR2 at hs hs' ⊢
  obtain ⟨hsR, hsN, hsV⟩ := hs
  obtain ⟨hsR', hsN', hsV'⟩ := hs'
  refine ⟨Rp.mul_mem hsR hsR', Subgroup.mul_mem _ hsN hsN', fun ω hω => ?_⟩
  have hc : s ∈ Subgroup.centralizer (V : Set G) := h.VRp hsR
  have e : ⁅ω, s * s'⁆ = ⁅ω, s⁆ * (s * ⁅ω, s'⁆ * s⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact V.mul_mem (hsV ω hω) (by rw [coreA_conj_eq hc (hsV' ω hω)]; exact hsV' ω hω)

theorem inR2_inv (h : CoreHyp R Rp H K Q LH V F α β) {s : G} (hs : InR2 R Rp V s) :
    InR2 R Rp V s⁻¹ := by
  unfold InR2 at hs ⊢
  obtain ⟨hsR, hsN, hsV⟩ := hs
  refine ⟨Rp.inv_mem hsR, Subgroup.inv_mem _ hsN, fun ω hω => ?_⟩
  have hc : s⁻¹ ∈ Subgroup.centralizer (V : Set G) := h.VRp (Rp.inv_mem hsR)
  have e : ⁅ω, s⁻¹⁆ = s⁻¹ * ⁅ω, s⁆⁻¹ * s⁻¹⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, coreA_conj_eq hc (V.inv_mem (hsV ω hω))]
  exact V.inv_mem (hsV ω hω)

theorem inR2_conj (h : CoreHyp R Rp H K Q LH V F α β) {s t : G} (hs : InR2 R Rp V s)
    (ht : t ∈ LH) : InR2 R Rp V (t * s * t⁻¹) := by
  unfold InR2 at hs ⊢
  obtain ⟨hsR, hsN, hsV⟩ := hs
  have htN : t ∈ Subgroup.normalizer (R : Set G) := h.LHR ht
  refine ⟨(Subgroup.mem_normalizer_iff.mp (h.LHRp ht) s).mp hsR,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ htN hsN) (Subgroup.inv_mem _ htN),
    fun ω hω => ?_⟩
  have htω : t⁻¹ * ω * t ∈ omegaOneCenterOf R := coreA_conj_omega_inv htN hω
  have e : ⁅ω, t * s * t⁻¹⁆ = t * ⁅t⁻¹ * ω * t, s⁆ * t⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (h.LHV ht) _).mp (hsV _ htω)

theorem inR2_comm (h : CoreHyp R Rp H K Q LH V F α β) {s h' : G} (hsR : s ∈ Rp)
    (hsN : s ∈ Subgroup.normalizer (R : Set G)) (hh : h' ∈ LH) :
    InR2 R Rp V (s * h' * s⁻¹ * h'⁻¹) := by
  unfold InR2
  have hconjRp : h' * s⁻¹ * h'⁻¹ ∈ Rp :=
    (Subgroup.mem_normalizer_iff.mp (h.LHRp hh) s⁻¹).mp (Rp.inv_mem hsR)
  have hconjN : h' * s⁻¹ * h'⁻¹ ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (h.LHR hh) (Subgroup.inv_mem _ hsN))
      (Subgroup.inv_mem _ (h.LHR hh))
  have ec : s * h' * s⁻¹ * h'⁻¹ = s * (h' * s⁻¹ * h'⁻¹) := by group
  refine ⟨by rw [ec]; exact Rp.mul_mem hsR hconjRp,
    by rw [ec]; exact Subgroup.mul_mem _ hsN hconjN, fun ω hω => ?_⟩
  have hsC : s ∈ Subgroup.centralizer (V : Set G) := h.VRp hsR
  have p₁Ω := coreA_conj_omega_inv (h.LHR hh) hω
  have E1 := coreA_F1' h hh hω
  have p₂Ω := coreA_conj_omega_inv hsN p₁Ω
  have E2 := coreA_F1 h hh p₂Ω
  have E3 := coreA_conj_E hsC E2
  have key : ⁅ω, s * h' * s⁻¹ * h'⁻¹⁆ = (ω * (h'⁻¹ * ω * h')⁻¹) *
      ((s * (s⁻¹ * (h'⁻¹ * ω * h') * s) * s⁻¹) *
        (s * (h' * (s⁻¹ * (h'⁻¹ * ω * h') * s) * h'⁻¹) * s⁻¹)⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [key]
  exact V.mul_mem E1 E3

theorem exists_inR2_not_mem (h : CoreHyp R Rp H K Q LH V F α β)
    (hZC : omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) ≠ ⊥) (hRlt : R < Rp) :
    ∃ s, InR2 R Rp V s ∧ s ∉ R := by
  by_contra hcon
  have hcon' : ∀ s, InR2 R Rp V s → s ∈ R := fun s hs =>
    Classical.byContradiction fun hsR => hcon ⟨s, hs, hsR⟩
  obtain ⟨s₀, hs₀Rp, hs₀N, hs₀R⟩ := CFSG.Quasithin.A4.exists_mem_normalizer_not_mem h.Rp2 hRlt
  apply hs₀R
  have hP : LH.map (MulAut.conj s₀).toMonoidHom ≤ R ⊔ LH := by
    rintro y ⟨k, hk, rfl⟩
    have hc : s₀ * k * s₀⁻¹ * k⁻¹ ∈ R := hcon' _ (inR2_comm h hs₀Rp hs₀N hk)
    show s₀ * k * s₀⁻¹ ∈ R ⊔ LH
    have e : s₀ * k * s₀⁻¹ = (s₀ * k * s₀⁻¹ * k⁻¹) * k := by group
    rw [e]
    exact (R ⊔ LH).mul_mem ((le_sup_left : R ≤ R ⊔ LH) hc) ((le_sup_right : LH ≤ R ⊔ LH) hk)
  have hPp : ⁅LH.map (MulAut.conj s₀).toMonoidHom, LH.map (MulAut.conj s₀).toMonoidHom⁆ =
      LH.map (MulAut.conj s₀).toMonoidHom := by
    rw [← Subgroup.map_commutator, h.LHp]
  have hRsolv : Group.IsSolvable R := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (h.Rp2.to_le h.RRp).isNilpotent
    infer_instance
  have hPLH : LH.map (MulAut.conj s₀).toMonoidHom ≤ LH :=
    le_of_perfect_of_le_sup_coreA hPp h.RLH hRsolv hP
  have hinj : Function.Injective (MulAut.conj s₀).toMonoidHom := (MulAut.conj s₀).injective
  have hEq : LH.map (MulAut.conj s₀).toMonoidHom = LH :=
    Subgroup.eq_of_le_of_card_ge hPLH (le_of_eq (Subgroup.card_map_of_injective hinj).symm)
  have hs₀LH : s₀ ∈ Subgroup.normalizer (LH : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hmem : s₀ * x * s₀⁻¹ ∈ LH.map (MulAut.conj s₀).toMonoidHom := ⟨x, hx, rfl⟩
      rw [hEq] at hmem
      exact hmem
    · intro hx
      have hmem : s₀ * x * s₀⁻¹ ∈ LH.map (MulAut.conj s₀).toMonoidHom := by
        rw [hEq]; exact hx
      obtain ⟨k, hk, hkx⟩ := hmem
      have hkx' : s₀ * k * s₀⁻¹ = s₀ * x * s₀⁻¹ := hkx
      have hkx'' : k = x := mul_left_cancel (mul_right_cancel hkx')
      rw [← hkx'']
      exact hk
  have hs₀C : s₀ ∈ Subgroup.normalizer ((Subgroup.centralizer (LH : Set G) : Subgroup G) :
      Set G) :=
    coreA_normalizer_centralizer hs₀LH
  have hs₀Ω : s₀ ∈ Subgroup.normalizer (omegaOneCenterOf R : Set G) :=
    CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf R hs₀N
  have hEqZ : omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) =
      omegaOneCenterOf R ⊓ Subgroup.centralizer (LH : Set G) := by
    apply le_antisymm
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1,
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.LHK) (Subgroup.mem_inf.mp hx).2⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, h.LH_C hx⟩
  have hs₀ZN : s₀ ∈ Subgroup.normalizer
      ((omegaOneCenterOf R ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
    rw [hEqZ]
    have hmem : s₀ ∈ Subgroup.normalizer (omegaOneCenterOf R : Set G) ⊓
        Subgroup.normalizer ((Subgroup.centralizer (LH : Set G) : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hs₀Ω, hs₀C⟩
    exact Subgroup.inf_normalizer_le_normalizer_inf hmem
  have hs₀H : s₀ ∈ H := h.NZ hZC hs₀ZN
  exact h.RpH (Subgroup.mem_inf.mpr ⟨hs₀Rp, hs₀H⟩)

end Steps

end CFSG.Quasithin.H13.Ch4.CentK
