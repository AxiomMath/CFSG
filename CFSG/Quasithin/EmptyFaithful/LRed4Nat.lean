module

public import CFSG.Quasithin.EmptyFaithful.LRed4Alt
public import CFSG.Quasithin.EmptyFaithful.LRed4CTriv
public import CFSG.Quasithin.Background.FLc2Real
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.Background.B5Part3
public import CFSG.Quasithin.Background.FLcLn

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.FLc Matrix
open scoped commutatorElement

namespace LRed4

section Sym

variable {V : Type} [CommGroup V] {X : Subgroup (MulAut V)}

theorem commutator_le_self (X : Subgroup (MulAut V)) : ⁅X, X⁆ ≤ X :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)

theorem theta_mem_alt (θ : ↥X ≃* Equiv.Perm (Fin 8)) (k : MulAut V) (hk : k ∈ X) :
    k ∈ ⁅X, X⁆ ↔ θ ⟨k, hk⟩ ∈ alternatingGroup (Fin 8) := by
  have hA : commutator (Equiv.Perm (Fin 8)) = alternatingGroup (Fin 8) :=
    alternatingGroup.commutator_perm_eq (by simp)
  have h1 : (commutator ↥X).map X.subtype = ⁅X, X⁆ := Subgroup.map_subtype_commutator X
  have h2 : (commutator ↥X).map θ.toMonoidHom = alternatingGroup (Fin 8) := by
    rw [← hA, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
      MonoidHom.range_eq_top.2 θ.surjective, ← commutator_def]
  constructor
  · intro hmem
    rw [← h1] at hmem
    obtain ⟨c, hc, hck⟩ := Subgroup.mem_map.1 hmem
    have : c = ⟨k, hk⟩ := Subtype.ext hck
    rw [← h2]
    exact ⟨c, hc, by rw [this]; rfl⟩
  · intro hmem
    rw [← h2] at hmem
    obtain ⟨c, hc, hcθ⟩ := Subgroup.mem_map.1 hmem
    have : c = ⟨k, hk⟩ := θ.injective hcθ
    rw [← h1]
    exact ⟨c, hc, by rw [this]; rfl⟩

theorem perm_eq_one_of_comm_alt (σ : Equiv.Perm (Fin 8))
    (h : ∀ τ ∈ alternatingGroup (Fin 8), σ * τ = τ * σ) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  show σ i = i
  by_contra hne'
  have hfin : ∃ a b : Fin 8, a ≠ b ∧ a ≠ i ∧ a ≠ σ i ∧ b ≠ i ∧ b ≠ σ i := by
    have key : ∀ i j : Fin 8, ∃ a b : Fin 8, a ≠ b ∧ a ≠ i ∧ a ≠ j ∧ b ≠ i ∧ b ≠ j := by decide
    exact key i (σ i)
  obtain ⟨a, b, hab, hai, haj, hbi, hbj⟩ := hfin
  let c : Equiv.Perm (Fin 8) := Equiv.swap i a * Equiv.swap a b
  have hc : c ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hai.symm,
      Equiv.Perm.sign_swap hab]
    rfl
  have h1 := congrArg (fun p : Equiv.Perm (Fin 8) => p i) (h c hc)
  simp only [Equiv.Perm.mul_apply] at h1
  have hci : c i = a := by
    show Equiv.swap i a (Equiv.swap a b i) = a
    rw [Equiv.swap_apply_of_ne_of_ne hai.symm hbi.symm, Equiv.swap_apply_left]
  have hcj : c (σ i) = σ i := by
    show Equiv.swap i a (Equiv.swap a b (σ i)) = σ i
    rw [Equiv.swap_apply_of_ne_of_ne haj.symm hbj.symm,
      Equiv.swap_apply_of_ne_of_ne hne' haj.symm]
  have h2 : (σ * c) i = (c * σ) i := h1
  simp only [Equiv.Perm.mul_apply, hci, hcj] at h2
  exact hai (σ.injective h2)

theorem centralizer_comm_trivial (θ : ↥X ≃* Equiv.Perm (Fin 8)) :
    ∀ x ∈ X, (∀ k ∈ ⁅X, X⁆, x * k = k * x) → x = 1 := by
  intro x hx hcomm
  have h1 : θ ⟨x, hx⟩ = 1 := by
    apply perm_eq_one_of_comm_alt
    intro τ hτ
    obtain ⟨k, rfl⟩ := θ.surjective τ
    have hkK : (k : MulAut V) ∈ ⁅X, X⁆ := by
      rw [theta_mem_alt θ k k.2]
      exact hτ
    have := hcomm k hkK
    have h3 : (⟨x, hx⟩ : ↥X) * k = k * ⟨x, hx⟩ := Subtype.ext this
    rw [← map_mul, ← map_mul, h3]
  have h2 : (⟨x, hx⟩ : ↥X) = 1 := θ.injective (h1.trans (map_one θ).symm)
  exact congrArg Subtype.val h2

theorem exists_sylow_not_comm [Finite V] (θ : ↥X ≃* Equiv.Perm (Fin 8)) {S : Subgroup (MulAut V)}
    (hS : IsSylowTwoOf S X) : ∃ s ∈ S, s ∉ ⁅X, X⁆ := by
  by_contra hcon
  push Not at hcon
  have hSK : S ≤ ⁅X, X⁆ := hcon
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have hX : Nat.card ↥X = 40320 := by
    rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h1 : Nat.card ↥(S.subgroupOf X) * (S.subgroupOf X).index = Nat.card ↥X :=
    Subgroup.card_mul_index _
  have h2 : Nat.card ↥(S.subgroupOf X) = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
  have h3 : Nat.card ↥S ∣ 20160 := by
    rw [← card_comm_s8 θ]
    exact Subgroup.card_dvd_of_le hSK
  rw [h2, hk, hX] at h1
  rw [hk] at h3
  have hk6 : k ≤ 6 := by
    by_contra h
    push Not at h
    have : 2 ^ 7 ∣ 2 ^ k := Nat.pow_dvd_pow 2 h
    have := this.trans h3
    omega
  have hodd := hS.2.2
  interval_cases k <;> omega

end Sym

section Coord

@[expose] def deltaSL : SLt 4 →* SLt 4 where
  toFun g := (g⁻¹).transpose
  map_one' := by
    apply Subtype.ext
    simp [Matrix.SpecialLinearGroup.coe_transpose]
  map_mul' g h := by
    apply Subtype.ext
    simp [Matrix.SpecialLinearGroup.coe_transpose, _root_.mul_inv_rev, Matrix.transpose_mul]

theorem mat_deltaSL (g : SLt 4) : mat (deltaSL g) = (mat g⁻¹)ᵀ := rfl

theorem deltaSL_deltaSL (g : SLt 4) : deltaSL (deltaSL g) = g := by
  have h1 : deltaSL g * g.transpose = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, mat_deltaSL, Matrix.SpecialLinearGroup.coe_transpose]
    rw [← Matrix.transpose_mul, mat_mul_inv, Matrix.transpose_one]
    rfl
  have h2 : (deltaSL g)⁻¹ = g.transpose := inv_eq_of_mul_eq_one_right h1
  show ((deltaSL g)⁻¹).transpose = g
  rw [h2]
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_transpose]

structure NatCoord {V : Type} [CommGroup V] (ρ : SLt 4 →* MulAut V) (U : Subgroup V) where
  β : ↥U ≃* Multiplicative (Vt 4)
  inv : ∀ g : SLt 4, ∀ u ∈ U, ρ g u ∈ U
  eq : ∀ (g : SLt 4) (u : ↥U) (hu : ρ g (u : V) ∈ U),
    Multiplicative.toAdd (β ⟨ρ g (u : V), hu⟩) = mat g *ᵥ Multiplicative.toAdd (β u)

theorem natCoord_of_realizes {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : ↥(StatedSL 4 (ZMod 2)) →* ↥H}
    (h : (FFModel.nat (StatedSL 4 (ZMod 2))).RealizesVia H U ⊥ π) :
    Nonempty (NatCoord (rhoOf π) U) := by
  obtain ⟨β, hβs, hβk, hβe, hUinv, -⟩ := vmodel_of_realizes (natAct (StatedSL 4 (ZMod 2))) h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  have hbij : Function.Bijective β := ⟨hinj, hβs⟩
  refine ⟨⟨MulEquiv.ofBijective β hbij, fun g u hu => hUinv _ u hu, fun g u hu => ?_⟩⟩
  have h1 := hβe (specialLinearGroupEquivStatedSL 4 (ZMod 2) g) u hu
  refine (congrArg Multiplicative.toAdd h1).trans ?_
  simp only [natAct, toAdd_ofAdd]
  rw [specialLinearGroupEquivStatedSL_coe]
  rfl

theorem natCoord_of_dual {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : ↥(StatedSL 4 (ZMod 2)) →* ↥H}
    (h : (FFModel.dualNat (StatedSL 4 (ZMod 2))).RealizesVia H U ⊥ π) :
    Nonempty (NatCoord ((rhoOf π).comp deltaSL) U) := by
  obtain ⟨β, hβs, hβk, hβe, hUinv, -⟩ := vmodel_of_realizes (dualNatAct (StatedSL 4 (ZMod 2))) h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  have hbij : Function.Bijective β := ⟨hinj, hβs⟩
  refine ⟨⟨MulEquiv.ofBijective β hbij, fun g u hu => hUinv _ u hu, fun g u hu => ?_⟩⟩
  have h1 := hβe (specialLinearGroupEquivStatedSL 4 (ZMod 2) (deltaSL g)) u hu
  refine (congrArg Multiplicative.toAdd h1).trans ?_
  simp only [dualNatAct, toAdd_ofAdd]
  rw [← map_inv, specialLinearGroupEquivStatedSL_coe, ← mat_deltaSL, deltaSL_deltaSL]
  rfl

@[expose] def coordAut {V : Type} [CommGroup V] {ρ : SLt 4 →* MulAut V} {U : Subgroup V}
    (C : NatCoord ρ U) (b : ↥U ≃* ↥U) : Multiplicative (Vt 4) ≃* Multiplicative (Vt 4) :=
  C.β.symm.trans (b.trans C.β)

theorem twist_mat {V : Type} [CommGroup V] {K : Subgroup (MulAut V)}
    {ρ : SLt 4 →* MulAut V} {U : Subgroup V} (C : NatCoord ρ U) {s : MulAut V} (b : ↥U ≃* ↥U)
    (hb : ∀ k ∈ K, ∀ (u : ↥U) (hu : (s⁻¹ * k * s) (u : V) ∈ U),
      ((b ⟨(s⁻¹ * k * s) (u : V), hu⟩ : ↥U) : V) = k ((b u : ↥U) : V))
    {M : SLt 4} (hM : ∀ v : Vt 4, Multiplicative.toAdd (coordAut C b (Multiplicative.ofAdd v)) = mat M *ᵥ v)
    {g g' : SLt 4} (hk : ρ g ∈ K) (hg' : ρ g' = s⁻¹ * ρ g * s) :
    mat M * mat g' = mat g * mat M := by
  have hEx : ∀ u : ↥U, coordAut C b (C.β u) = C.β (b u) := fun u => by simp [coordAut]
  have hvec : ∀ x : Vt 4, mat M *ᵥ (mat g' *ᵥ x) = mat g *ᵥ (mat M *ᵥ x) := by
    intro x
    set u : ↥U := C.β.symm (Multiplicative.ofAdd x) with hu
    have hβu : C.β u = Multiplicative.ofAdd x := by simp [hu]
    have hu₁ : ρ g' (u : V) ∈ U := C.inv g' u u.2
    have hg'u : ρ g' (u : V) = (s⁻¹ * ρ g * s) (u : V) := by rw [hg']
    have hu₂ : (s⁻¹ * ρ g * s) (u : V) ∈ U := hg'u ▸ hu₁
    have e1 := C.eq g' u hu₁
    rw [hβu, toAdd_ofAdd] at e1
    have e2 : C.β ⟨ρ g' (u : V), hu₁⟩ = Multiplicative.ofAdd (mat g' *ᵥ x) := by
      apply Multiplicative.toAdd.injective
      rw [e1, toAdd_ofAdd]
    have e3 : coordAut C b (Multiplicative.ofAdd (mat g' *ᵥ x)) = C.β (b ⟨ρ g' (u : V), hu₁⟩) := by
      rw [← e2, hEx]
    have e4 : ((b ⟨ρ g' (u : V), hu₁⟩ : ↥U) : V) = ρ g ((b u : ↥U) : V) := by
      have := hb (ρ g) hk u hu₂
      have h5 : (⟨ρ g' (u : V), hu₁⟩ : ↥U) = ⟨(s⁻¹ * ρ g * s) (u : V), hu₂⟩ := Subtype.ext hg'u
      rw [h5]
      exact this
    have hbu : ρ g ((b u : ↥U) : V) ∈ U := C.inv g _ (b u).2
    have e5 : b ⟨ρ g' (u : V), hu₁⟩ = ⟨ρ g ((b u : ↥U) : V), hbu⟩ := Subtype.ext e4
    have e6 := C.eq g (b u) hbu
    have e7 := hM (mat g' *ᵥ x)
    have e8 := hM x
    rw [e3] at e7
    have e9 : C.β (b u) = coordAut C b (Multiplicative.ofAdd x) := by rw [← hβu, hEx]
    calc mat M *ᵥ mat g' *ᵥ x = Multiplicative.toAdd (C.β (b ⟨ρ g' (u : V), hu₁⟩)) := e7.symm
      _ = Multiplicative.toAdd (C.β ⟨ρ g ((b u : ↥U) : V), hbu⟩) := by rw [e5]
      _ = mat g *ᵥ Multiplicative.toAdd (C.β (b u)) := e6
      _ = mat g *ᵥ (mat M *ᵥ x) := by rw [e9, e8]
  apply Matrix.ext
  intro i j
  have h := congrFun (hvec (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one] at h
  simpa using h

theorem twist {V : Type} [CommGroup V] {X K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hnorm : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hcent : ∀ x ∈ X, (∀ k ∈ K, x * k = k * x) → x = 1)
    {ρ : SLt 4 →* MulAut V} (hρK : ∀ g, ρ g ∈ K) (hρs : ∀ k ∈ K, ∃ g, ρ g = k)
    {U : Subgroup V} (C : NatCoord ρ U) {s : MulAut V} (hs : s ∈ X) (b : ↥U ≃* ↥U)
    (hb : ∀ k ∈ K, ∀ (u : ↥U) (hu : (s⁻¹ * k * s) (u : V) ∈ U),
      ((b ⟨(s⁻¹ * k * s) (u : V), hu⟩ : ↥U) : V) = k ((b u : ↥U) : V)) : s ∈ K := by
  obtain ⟨M, hM⟩ := exists_mat_of_mulEquiv (coordAut C b)
  have key : ∀ k ∈ K, s⁻¹ * k * s = (ρ M)⁻¹ * k * ρ M := by
    intro k hk
    obtain ⟨g, rfl⟩ := hρs k hk
    have hk' : s⁻¹ * ρ g * s ∈ K := by
      have := hnorm s⁻¹ (X.inv_mem hs) (ρ g) hk
      simpa using this
    obtain ⟨g', hg'⟩ := hρs _ hk'
    have hmat := twist_mat C b hb hM hk hg'
    have hSL : M * g' = g * M := Subtype.ext hmat
    have hg'eq : g' = M⁻¹ * g * M := by
      rw [mul_assoc]; exact (inv_mul_eq_iff_eq_mul.2 hSL.symm).symm
    calc s⁻¹ * ρ g * s = ρ g' := hg'.symm
      _ = (ρ M)⁻¹ * ρ g * ρ M := by rw [hg'eq, map_mul, map_mul, map_inv]
  have hμK : ρ M ∈ K := hρK M
  have hc : s * (ρ M)⁻¹ ∈ X := X.mul_mem hs (X.inv_mem (hKX hμK))
  have hcomm : ∀ k ∈ K, s * (ρ M)⁻¹ * k = k * (s * (ρ M)⁻¹) := by
    intro k hk
    have h1 := key k hk
    have h2 : k * s = s * ((ρ M)⁻¹ * k * ρ M) := by rw [← h1]; group
    calc s * (ρ M)⁻¹ * k = s * ((ρ M)⁻¹ * k * ρ M) * (ρ M)⁻¹ := by group
      _ = k * s * (ρ M)⁻¹ := by rw [← h2]
      _ = k * (s * (ρ M)⁻¹) := by group
  have h1 := hcent _ hc hcomm
  have hs' : s = ρ M := by
    have : s = s * (ρ M)⁻¹ * ρ M := by group
    rw [this, h1, one_mul]
  rw [hs']
  exact hμK

section NatK

variable {V : Type} [CommGroup V]

@[expose] def conjSub (s : MulAut V) (I : Subgroup V) : Subgroup V :=
  I.map (s : V ≃* V).toMonoidHom

theorem mem_conjSub {s : MulAut V} {I : Subgroup V} {x : V} :
    x ∈ conjSub s I ↔ ∃ u ∈ I, s u = x := by
  simp [conjSub, Subgroup.mem_map]

theorem isInv_conjSub {K : Subgroup (MulAut V)} {I : Subgroup V} {s : MulAut V}
    (hn : ∀ k ∈ K, s⁻¹ * k * s ∈ K) (hI : XMod.IsInv ↥K I) : XMod.IsInv ↥K (conjSub s I) := by
  intro a x hx
  obtain ⟨u, hu, rfl⟩ := mem_conjSub.1 hx
  refine mem_conjSub.2 ⟨(s⁻¹ * (a : MulAut V) * s) u, ?_, ?_⟩
  · exact hI ⟨s⁻¹ * (a : MulAut V) * s, hn _ a.2⟩ u hu
  · show s ((s⁻¹ * (a : MulAut V) * s) u) = (a : MulAut V) (s u)
    simp [mul_assoc]

theorem isIrr_conjSub {K : Subgroup (MulAut V)} {I : Subgroup V} {s : MulAut V}
    (hn : ∀ k ∈ K, s⁻¹ * k * s ∈ K) (hn' : ∀ k ∈ K, s * k * s⁻¹ ∈ K) (hI : XMod.IsIrr ↥K I) :
    XMod.IsIrr ↥K (conjSub s I) := by
  refine ⟨isInv_conjSub hn hI.1, ?_, ?_⟩
  · refine bot_lt_iff_ne_bot.2 fun hb => ?_
    have := hI.2.1
    apply this.ne
    symm
    rw [eq_bot_iff]
    intro x hx
    have : s x ∈ conjSub s I := mem_conjSub.2 ⟨x, hx, rfl⟩
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (s.injective (this.trans (map_one s).symm))
  · intro J hJ _ hJI
    have hJ' : XMod.IsInv ↥K (conjSub s⁻¹ J) := isInv_conjSub (K := K) (s := s⁻¹)
      (fun k hk => by simpa using hn' k hk) hJ
    have hle : conjSub s⁻¹ J ≤ I := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := mem_conjSub.1 hx
      obtain ⟨w, hw, hwu⟩ := mem_conjSub.1 (hJI hu)
      have : s⁻¹ u = w := by rw [← hwu]; exact MulAut.inv_apply_self V s w
      rw [this]; exact hw
    rcases hI.2.2 _ hJ' bot_le hle with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have : s⁻¹ x ∈ conjSub s⁻¹ J := mem_conjSub.2 ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (by simpa using this)
    · right
      refine le_antisymm hJI fun x hx => ?_
      obtain ⟨w, hw, rfl⟩ := mem_conjSub.1 hx
      have : w ∈ conjSub s⁻¹ J := by rw [h]; exact hw
      obtain ⟨u, hu, hu'⟩ := mem_conjSub.1 this
      have : s w = u := by rw [← hu']; exact MulAut.apply_inv_self V s u
      rw [this]; exact hu

end NatK

section NatCopies

variable {V : Type} [CommGroup V]

theorem not_directSum_nat {X : Subgroup (MulAut V)}
    (hnorm : ∀ x ∈ X, ∀ k ∈ ⁅X, X⁆, x * k * x⁻¹ ∈ ⁅X, X⁆)
    (hcent : ∀ x ∈ X, (∀ k ∈ ⁅X, X⁆, x * k = k * x) → x = 1)
    {s : MulAut V} (hs : s ∈ X) (hsK : s ∉ ⁅X, X⁆) (k : ℕ) (hk1 : 1 ≤ k) :
    ¬ DirectSumOfCopies ⁅X, X⁆ ⊤ ⊥ (FFModel.nat (StatedSL 4 (ZMod 2))) k := by
  rintro ⟨I, π, -, -, hsup, hreal⟩
  have hKX : ⁅X, X⁆ ≤ X := commutator_le_self X
  have hn : ∀ k ∈ ⁅X, X⁆, s⁻¹ * k * s ∈ ⁅X, X⁆ := fun k hk => by
    have := hnorm s⁻¹ (X.inv_mem hs) k hk
    simpa using this
  have hn' : ∀ k ∈ ⁅X, X⁆, s * k * s⁻¹ ∈ ⁅X, X⁆ := fun k hk => hnorm s hs k hk
  let i₀ : Fin k := ⟨0, hk1⟩
  have hπ : Function.Surjective π := (hreal i₀).1
  obtain ⟨C⟩ := natCoord_of_realizes (hreal i₀)
  have hirr : ∀ i, XMod.IsIrr ↥⁅X, X⁆ (I i) := fun i => B5.isIrr_of_realizes (by norm_num) (hreal i)
  have hiso : ∀ i j, XMod.Iso ↥⁅X, X⁆ (I i) (I j) := fun i j => B5.iso_of_realizes hπ (hreal i) (hreal j)
  have hJirr : XMod.IsIrr ↥⁅X, X⁆ (conjSub s (I i₀)) := isIrr_conjSub hn hn' (hirr i₀)
  have hJU : conjSub s (I i₀) ≤ ⨆ i, I i := by
    have h1 : (⨆ i, I i) = ⊤ := by
      have := hsup
      rwa [bot_sup_eq] at this
    rw [h1]
    exact le_top
  obtain ⟨φ, hφ⟩ := B5.iso_of_irr_le_iSup I hirr hiso i₀ hJirr hJU
  let e : ↥(I i₀) ≃* ↥(conjSub s (I i₀)) :=
    Subgroup.equivMapOfInjective (I i₀) (s : V ≃* V).toMonoidHom s.injective
  let b : ↥(I i₀) ≃* ↥(I i₀) := e.trans φ
  refine hsK (twist hKX hnorm hcent (rhoOf_mem π) (rhoOf_surj hπ) C hs b ?_)
  intro k hk u hu
  have hl : s (u : V) ∈ conjSub s (I i₀) := mem_conjSub.2 ⟨u, u.2, rfl⟩
  have hl' : k (s (u : V)) ∈ conjSub s (I i₀) := hJirr.1 ⟨k, hk⟩ _ hl
  have h1 := hφ ⟨k, hk⟩ ⟨s (u : V), hl⟩ ⟨k (s (u : V)), hl'⟩ rfl
  have e1 : e u = ⟨s (u : V), hl⟩ := Subtype.ext rfl
  have e2 : e ⟨(s⁻¹ * k * s) (u : V), hu⟩ = ⟨k (s (u : V)), hl'⟩ := by
    apply Subtype.ext
    show s ((s⁻¹ * k * s) (u : V)) = k (s (u : V))
    show (s * (s⁻¹ * k * s)) (u : V) = (k * s) (u : V)
    rw [mul_assoc, mul_inv_cancel_left]
  show ((φ (e ⟨(s⁻¹ * k * s) (u : V), hu⟩) : ↥(I i₀)) : V) = k ((φ (e u) : ↥(I i₀)) : V)
  rw [e2, e1]
  exact h1.symm

end NatCopies

theorem natAct_eq_actM (g : SLt 4) (x : Multiplicative (Vt 4)) :
    natAct (StatedSL 4 (ZMod 2)) (specialLinearGroupEquivStatedSL 4 (ZMod 2) g) x = actM g x := by
  apply Multiplicative.toAdd.injective
  simp only [natAct, toAdd_ofAdd, toAdd_actM]
  rw [specialLinearGroupEquivStatedSL_coe]

section CoordLemmas

variable {V : Type} [CommGroup V]

theorem isIrr_of_coord {K : Subgroup (MulAut V)} {ρ : SLt 4 →* MulAut V} (hρK : ∀ g, ρ g ∈ K)
    (hρs : ∀ k ∈ K, ∃ g, ρ g = k) {U : Subgroup V} (C : NatCoord ρ U) : XMod.IsIrr ↥K U := by
  have hinv : XMod.IsInv ↥K U := by
    intro a u hu
    obtain ⟨g, hg⟩ := hρs a a.2
    show (a : MulAut V) u ∈ U
    rw [← hg]
    exact C.inv g u hu
  refine ⟨hinv, bot_lt_iff_ne_bot.2 fun hbot => ?_, ?_⟩
  · have hsub : Subsingleton ↥U := by rw [hbot]; infer_instance
    have : Subsingleton (Multiplicative (Vt 4)) := C.β.symm.injective.subsingleton
    have hnt : Nontrivial (Multiplicative (Vt 4)) := by infer_instance
    exact (not_subsingleton _) this
  · intro J hJ _ hJU
    let J' : Subgroup (Multiplicative (Vt 4)) := (J.subgroupOf U).map C.β.toMonoidHom
    have hJ' : ∀ (γ : ↥(StatedSL 4 (ZMod 2))) (x : Multiplicative (Fin 4 → ZMod 2)), x ∈ J' →
        natAct (StatedSL 4 (ZMod 2)) γ x ∈ J' := by
      intro γ x hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
      have huJ : (u : V) ∈ J := Subgroup.mem_subgroupOf.1 hu
      set g := (specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm γ with hg
      have hγ : γ = specialLinearGroupEquivStatedSL 4 (ZMod 2) g := by simp [hg]
      have hρJ : ρ g (u : V) ∈ J := hJ ⟨ρ g, hρK g⟩ _ huJ
      have hρU : ρ g (u : V) ∈ U := C.inv g u u.2
      refine Subgroup.mem_map.2 ⟨⟨ρ g (u : V), hρU⟩, Subgroup.mem_subgroupOf.2 hρJ, ?_⟩
      rw [hγ, natAct_eq_actM]
      apply Multiplicative.toAdd.injective
      exact C.eq g u hρU
    rcases B5.natural_invariant_eq (by norm_num) J' hJ' with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      have h1 : (⟨w, hJU hw⟩ : ↥U) ∈ J.subgroupOf U := hw
      have h2 : C.β ⟨w, hJU hw⟩ ∈ J' := Subgroup.mem_map_of_mem _ h1
      rw [h, Subgroup.mem_bot] at h2
      have h3 : (⟨w, hJU hw⟩ : ↥U) = 1 := C.β.injective (h2.trans (map_one C.β).symm)
      exact Subgroup.mem_bot.2 (congrArg Subtype.val h3)
    · right
      refine le_antisymm hJU fun w hw => ?_
      have hmem : C.β ⟨w, hw⟩ ∈ J' := by rw [h]; trivial
      obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.1 hmem
      have : u = ⟨w, hw⟩ := C.β.injective hue
      rw [this] at hu
      exact Subgroup.mem_subgroupOf.1 hu

def NatCoord.conj {ρ : SLt 4 →* MulAut V} {U : Subgroup V} (C : NatCoord ρ U) (g : SLt 4) :
    NatCoord (ρ.comp (MulAut.conj g).toMonoidHom) U where
  β := C.β.trans (actM g⁻¹)
  inv := fun h u hu => C.inv (g * h * g⁻¹) u hu
  eq := fun h u hu => by
    have h1 := C.eq (g * h * g⁻¹) u hu
    show Multiplicative.toAdd (actM g⁻¹ (C.β ⟨ρ (g * h * g⁻¹) (u : V), hu⟩)) = _
    rw [toAdd_actM, h1]
    show mat g⁻¹ *ᵥ (mat (g * h * g⁻¹) *ᵥ Multiplicative.toAdd (C.β u)) =
      mat h *ᵥ (mat g⁻¹ *ᵥ Multiplicative.toAdd (C.β u))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mat_inv_conj_mul]

section Proj

variable {V : Type} [CommGroup V]

theorem exists_proj {U₁ U₂ : Subgroup V} (h : IsIntDirect U₁ U₂ ⊤) :
    ∃ p : V →* V, (∀ v, p v ∈ U₁) ∧ (∀ a ∈ U₁, ∀ b ∈ U₂, p (a * b) = a) := by
  classical
  have hex : ∀ v : V, ∃ a ∈ U₁, ∃ b ∈ U₂, a * b = v := fun v => by
    have : v ∈ U₁ ⊔ U₂ := by rw [h.1]; trivial
    exact Subgroup.mem_sup.1 this
  have huniq : ∀ a ∈ U₁, ∀ a' ∈ U₁, ∀ b ∈ U₂, ∀ b' ∈ U₂, a * b = a' * b' → a = a' := by
    intro a ha a' ha' b hb b' hb' hab
    have h1 : a'⁻¹ * a ∈ U₁ ⊓ U₂ := by
      refine ⟨U₁.mul_mem (U₁.inv_mem ha') ha, ?_⟩
      have : a'⁻¹ * a = b' * b⁻¹ := by
        calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
          _ = b' * b⁻¹ := by rw [hab]; group
      rw [this]
      exact U₂.mul_mem hb' (U₂.inv_mem hb)
    rw [h.2, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.1 h1).symm
  let p : V → V := fun v => (hex v).choose
  have hp1 : ∀ v, p v ∈ U₁ := fun v => (hex v).choose_spec.1
  have hp2 : ∀ v, ∃ b ∈ U₂, p v * b = v := fun v => (hex v).choose_spec.2
  have hpe : ∀ a ∈ U₁, ∀ b ∈ U₂, p (a * b) = a := by
    intro a ha b hb
    obtain ⟨b', hb', hb''⟩ := hp2 (a * b)
    exact huniq _ (hp1 _) a ha b' hb' b hb hb''
  refine ⟨{ toFun := p, map_one' := ?_, map_mul' := ?_ }, hp1, hpe⟩
  · have := hpe 1 U₁.one_mem 1 U₂.one_mem
    simpa using this
  · intro v w
    obtain ⟨b, hb, hbv⟩ := hp2 v
    obtain ⟨b', hb', hbw⟩ := hp2 w
    have : v * w = (p v * p w) * (b * b') := by
      calc v * w = (p v * b) * (p w * b') := by rw [hbv, hbw]
        _ = _ := by ac_rfl
    show p (v * w) = p v * p w
    rw [this]
    exact hpe _ (U₁.mul_mem (hp1 v) (hp1 w)) _ (U₂.mul_mem hb hb')

theorem inf_eq_bot_or_le [Finite V] {V₂ W : Subgroup V} {y : MulAut V} (hV₂ : Nat.card ↥V₂ = 4)
    (hyW : ∀ w ∈ W, y w ∈ W) (hyV₂ : ∀ v ∈ V₂, y v ∈ V₂) (hyfix : ∀ v ∈ V₂, y v = v → v = 1) :
    V₂ ⊓ W = ⊥ ∨ V₂ ≤ W := by
  by_cases hb : V₂ ⊓ W = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hb
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hyw : y w ∈ V₂ ⊓ W := ⟨hyV₂ w hw.1, hyW w hw.2⟩
  have hne : y w ≠ w := fun h => hw1' (hyfix w hw.1 h)
  have hy1 : y w ≠ 1 := fun h => hw1' (y.injective (h.trans (map_one y).symm))
  have h3 := three_le_card (G := ↥(V₂ ⊓ W)) (a := ⟨1, (V₂ ⊓ W).one_mem⟩) (b := ⟨w, hw⟩)
    (c := ⟨y w, hyw⟩) (fun h => hw1' (congrArg Subtype.val h).symm)
    (fun h => hy1 (congrArg Subtype.val h).symm) (fun h => hne (congrArg Subtype.val h).symm)
  have hdvd : Nat.card ↥(V₂ ⊓ W) ∣ 4 := hV₂ ▸ Subgroup.card_dvd_of_le inf_le_left
  have hle4 : Nat.card ↥(V₂ ⊓ W) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have heq : Nat.card ↥(V₂ ⊓ W) = 4 := by
    interval_cases h : Nat.card ↥(V₂ ⊓ W) <;> simp_all
  have : V₂ ⊓ W = V₂ := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [heq, hV₂])
  rw [← this]
  exact inf_le_right

end Proj

section CaseA

variable {V : Type} [CommGroup V]

theorem false_of_le_natural [Finite V] {X K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hnorm : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (hcent : ∀ x ∈ X, (∀ k ∈ K, x * k = k * x) → x = 1)
    {ρ : SLt 4 →* MulAut V} (hρK : ∀ g, ρ g ∈ K) (hρs : ∀ k ∈ K, ∃ g, ρ g = k)
    {U : Subgroup V} (C : NatCoord ρ U) {V₂ : Subgroup V} {s : MulAut V} (hs : s ∈ X) (hsK : s ∉ K)
    (hsV₂ : ∀ v ∈ V₂, s v ∈ V₂) (hV₂U : V₂ ≤ U) (hV₂ne : V₂ ≠ ⊥) : False := by
  have hn : ∀ k ∈ K, s⁻¹ * k * s ∈ K := fun k hk => by
    have := hnorm s⁻¹ (X.inv_mem hs) k hk
    simpa using this
  have hcardU : ∀ W : Subgroup V, Nat.card ↥(conjSub s W) = Nat.card ↥W := fun W =>
    Subgroup.card_map_of_injective s.injective
  have hV₂s : conjSub s V₂ = V₂ := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [hcardU])
    obtain ⟨u, hu, rfl⟩ := mem_conjSub.1 hx
    exact hsV₂ u hu
  have hirr := isIrr_of_coord hρK hρs C
  have hUinv : XMod.IsInv ↥K U := hirr.1
  have hJinv : XMod.IsInv ↥K (U ⊓ conjSub s U) := fun a x hx =>
    ⟨hUinv a x hx.1, isInv_conjSub hn hUinv a x hx.2⟩
  have hV₂J : V₂ ≤ U ⊓ conjSub s U := fun x hx =>
    ⟨hV₂U hx, by
      have : x ∈ conjSub s V₂ := by rw [hV₂s]; exact hx
      obtain ⟨u, hu, rfl⟩ := mem_conjSub.1 this
      exact mem_conjSub.2 ⟨u, hV₂U hu, rfl⟩⟩
  have hJU : U ⊓ conjSub s U = U := by
    rcases hirr.2.2 _ hJinv bot_le inf_le_left with h | h
    · exact absurd (eq_bot_iff.2 (h ▸ hV₂J)) hV₂ne
    · exact h
  have hUle : U ≤ conjSub s U := by
    intro x hx
    have : x ∈ U ⊓ conjSub s U := by rw [hJU]; exact hx
    exact this.2
  have hUeq : conjSub s U = U :=
    (Subgroup.eq_of_le_of_card_ge hUle (by rw [hcardU])).symm
  have hs₁ : ∀ u ∈ U, s u ∈ U := fun u hu => by
    have : s u ∈ conjSub s U := mem_conjSub.2 ⟨u, hu, rfl⟩
    rwa [hUeq] at this
  have hs₂ : ∀ u ∈ U, s⁻¹ u ∈ U := fun u hu => by
    have : u ∈ conjSub s U := by rw [hUeq]; exact hu
    obtain ⟨w, hw, rfl⟩ := mem_conjSub.1 this
    rw [MulAut.inv_apply_self V s w]
    exact hw
  let b : ↥U ≃* ↥U :=
    { toFun := fun u => ⟨s (u : V), hs₁ _ u.2⟩
      invFun := fun u => ⟨s⁻¹ (u : V), hs₂ _ u.2⟩
      left_inv := fun u => Subtype.ext (MulAut.inv_apply_self V s _)
      right_inv := fun u => Subtype.ext (MulAut.apply_inv_self V s _)
      map_mul' := fun u w => Subtype.ext (map_mul s _ _) }
  refine hsK (twist hKX hnorm hcent hρK hρs C hs b ?_)
  intro k hk u hu
  show s ((s⁻¹ * k * s) (u : V)) = k (s (u : V))
  show (s * (s⁻¹ * k * s)) (u : V) = (k * s) (u : V)
  rw [mul_assoc, mul_inv_cancel_left]

end CaseA

section Transv

@[expose] def tv (j : Fin 4) (hj : j ≠ 0) : SLt 4 :=
  ⟨Matrix.transvection 0 j 1, by rw [Matrix.det_transvection_of_ne 0 j (Ne.symm hj)]⟩

theorem tv_mem_Ut (j : Fin 4) (hj : j ≠ 0) : tv j hj ∈ Ut 4 := by
  have key1 : ∀ j : Fin 4, j ≠ 0 → ∀ p : Fin 4 × Fin 4, p.2 < p.1 →
      (1 + Matrix.single 0 j (1 : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2)) p.1 p.2 = 0 := by
    decide +kernel
  have key2 : ∀ j : Fin 4, j ≠ 0 → ∀ i : Fin 4,
      (1 + Matrix.single 0 j (1 : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2)) i i = 1 := by
    decide +kernel
  exact ⟨fun i k hik => key1 j hj (i, k) hik, key2 j hj⟩

theorem tv_mulVec (j : Fin 4) (hj : j ≠ 0) (w : Vt 4) :
    mat (tv j hj) *ᵥ w = w + Pi.single 0 (w j) := by
  have key : ∀ j : Fin 4, j ≠ 0 → ∀ w : Vt 4,
      (1 + Matrix.single 0 j (1 : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w =
        w + Pi.single 0 (w j) := by
    decide +kernel
  exact key j hj w

theorem tv_inv (j : Fin 4) (hj : j ≠ 0) : (tv j hj)⁻¹ = tv j hj := by
  have key : ∀ j : Fin 4, j ≠ 0 →
      (1 + Matrix.single 0 j (1 : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        (1 + Matrix.single 0 j (1 : ZMod 2)) = 1 := by
    decide +kernel
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  exact key j hj

theorem delta_tv_mulVec (j : Fin 4) (hj : j ≠ 0) (w : Vt 4) :
    mat (deltaSL (tv j hj)) *ᵥ w = w + Pi.single j (w 0) := by
  rw [mat_deltaSL, tv_inv]
  have key : ∀ j : Fin 4, j ≠ 0 → ∀ w : Vt 4,
      (1 + Matrix.single 0 j (1 : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ *ᵥ w =
        w + Pi.single j (w 0) := by
    decide +kernel
  exact key j hj w

end Transv

section CaseB

variable {V : Type} [CommGroup V]

theorem NatCoord.dual_eq {ρ ρ₂ : SLt 4 →* MulAut V} (hρ₂ : ∀ h, ρ₂ h = ρ (deltaSL h)) {U : Subgroup V}
    (C : NatCoord ρ₂ U) (h : SLt 4) (u : ↥U) (hu : ρ h (u : V) ∈ U) :
    Multiplicative.toAdd (C.β ⟨ρ h (u : V), hu⟩) =
      mat (deltaSL h) *ᵥ Multiplicative.toAdd (C.β u) := by
  have hρh : ρ₂ (deltaSL h) = ρ h := by rw [hρ₂, deltaSL_deltaSL]
  have hu' : ρ₂ (deltaSL h) (u : V) ∈ U := by rw [hρh]; exact hu
  have h1 := C.eq (deltaSL h) u hu'
  have h2 : (⟨ρ h (u : V), hu⟩ : ↥U) = ⟨ρ₂ (deltaSL h) (u : V), hu'⟩ :=
    Subtype.ext (by show (ρ h) (u : V) = (ρ₂ (deltaSL h)) (u : V); rw [hρh])
  rw [h2]
  exact h1

theorem NatCoord.dual_inv {ρ ρ₂ : SLt 4 →* MulAut V} (hρ₂ : ∀ h, ρ₂ h = ρ (deltaSL h)) {U : Subgroup V}
    (C : NatCoord ρ₂ U) (h : SLt 4) (u : V) (hu : u ∈ U) : ρ h u ∈ U := by
  have := C.inv (deltaSL h) u hu
  rwa [hρ₂, deltaSL_deltaSL] at this

theorem card_map_le' {G H : Type} [Group G] [Group H] [Finite G] (f : G →* H) (K : Subgroup G) :
    Nat.card ↥(K.map f) ≤ Nat.card ↥K := by
  refine Nat.card_le_card_of_surjective (fun x : ↥K => (⟨f x, ⟨x, x.2, rfl⟩⟩ : ↥(K.map f))) ?_
  rintro ⟨_, ⟨x, hx, rfl⟩⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem false_of_graph [Finite V] {ρ ρ₂ : SLt 4 →* MulAut V} {U₁ U₂ : Subgroup V}
    (hdir : IsIntDirect U₁ U₂ ⊤) (C₁ : NatCoord ρ U₁) (hρ₂ : ∀ h, ρ₂ h = ρ (deltaSL h))
    (C₂ : NatCoord ρ₂ U₂)
    {V₂ : Subgroup V} (hV₂ : Nat.card ↥V₂ = 4)
    (hinv : ∀ h ∈ Ut 4, ∀ v ∈ V₂, ρ h v ∈ V₂) (h1 : V₂ ⊓ U₁ = ⊥) (h2 : V₂ ⊓ U₂ = ⊥) : False := by
  obtain ⟨p, hp1, hpe⟩ := exists_proj hdir
  have hdec : ∀ v : V, v * (p v)⁻¹ ∈ U₂ := by
    intro v
    have hv : v ∈ U₁ ⊔ U₂ := by rw [hdir.1]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hv
    rw [← hab, hpe a ha b hb]
    have : a * b * a⁻¹ = b := by rw [mul_comm a b, mul_inv_cancel_right]
    rw [this]
    exact hb
  let q : V →* V := MonoidHom.id V / p
  have hq : ∀ v, q v = v * (p v)⁻¹ := fun v => div_eq_mul_inv _ _
  have hq2 : ∀ v, q v ∈ U₂ := fun v => by rw [hq]; exact hdec v
  have hpq : ∀ v, v = p v * q v := fun v => by
    rw [hq]
    exact (by rw [mul_left_comm, mul_inv_cancel, mul_one] : p v * (v * (p v)⁻¹) = v).symm
  have hp_eq : ∀ (h : SLt 4) (v : V), p (ρ h v) = ρ h (p v) := by
    intro h v
    have hq' : ρ h (q v) ∈ U₂ := C₂.dual_inv hρ₂ h _ (hq2 v)
    have hq1 : ρ h (p v) ∈ U₁ := C₁.inv h _ (hp1 v)
    have : ρ h v = ρ h (p v) * ρ h (q v) := by rw [← map_mul, ← hpq v]
    rw [this]
    exact hpe _ hq1 _ hq'
  have hq_eq : ∀ (h : SLt 4) (v : V), q (ρ h v) = ρ h (q v) := by
    intro h v
    rw [hq, hq, hp_eq, map_mul, map_inv]
  let p₁ : V →* ↥U₁ := p.codRestrict U₁ hp1
  let p₂ : V →* ↥U₂ := q.codRestrict U₂ hq2
  let φ₁ : V →* Multiplicative (Vt 4) := C₁.β.toMonoidHom.comp p₁
  let φ₂ : V →* Multiplicative (Vt 4) := C₂.β.toMonoidHom.comp p₂
  have hφ₁eq : ∀ (h : SLt 4) (v : V),
      Multiplicative.toAdd (φ₁ (ρ h v)) = mat h *ᵥ Multiplicative.toAdd (φ₁ v) := by
    intro h v
    have hmem : ρ h (p v) ∈ U₁ := C₁.inv h _ (hp1 v)
    have h3 := C₁.eq h ⟨p v, hp1 v⟩ hmem
    have h4 : (p₁ (ρ h v) : ↥U₁) = ⟨ρ h (p v), hmem⟩ := Subtype.ext (hp_eq h v)
    show Multiplicative.toAdd (C₁.β (p₁ (ρ h v))) = _
    rw [h4]
    exact h3
  have hφ₂eq : ∀ (h : SLt 4) (v : V),
      Multiplicative.toAdd (φ₂ (ρ h v)) = mat (deltaSL h) *ᵥ Multiplicative.toAdd (φ₂ v) := by
    intro h v
    have hmem : ρ h (q v) ∈ U₂ := C₂.dual_inv hρ₂ h _ (hq2 v)
    have h3 := C₂.dual_eq hρ₂ h ⟨q v, hq2 v⟩ hmem
    have h4 : (p₂ (ρ h v) : ↥U₂) = ⟨ρ h (q v), hmem⟩ := Subtype.ext (hq_eq h v)
    show Multiplicative.toAdd (C₂.β (p₂ (ρ h v))) = _
    rw [h4]
    exact h3
  have hφ₁ker : ∀ v ∈ V₂, φ₁ v = 1 → v = 1 := by
    intro v hv hφ
    have h5 : p₁ v = 1 := C₁.β.injective (hφ.trans (map_one C₁.β).symm)
    have h6 : p v = 1 := congrArg Subtype.val h5
    have h7 : v ∈ U₂ := by
      have := hq2 v
      rwa [hq, h6, inv_one, mul_one] at this
    have : v ∈ V₂ ⊓ U₂ := ⟨hv, h7⟩
    rw [h2, Subgroup.mem_bot] at this
    exact this
  have hφ₂ker : ∀ v ∈ V₂, φ₂ v = 1 → v = 1 := by
    intro v hv hφ
    have h5 : p₂ v = 1 := C₂.β.injective (hφ.trans (map_one C₂.β).symm)
    have h6 : q v = 1 := congrArg Subtype.val h5
    have h7 : v ∈ U₁ := by
      have h8 : v = p v := by
        have := hpq v
        rw [h6, mul_one] at this
        exact this
      rw [h8]
      exact hp1 v
    have : v ∈ V₂ ⊓ U₁ := ⟨hv, h7⟩
    rw [h1, Subgroup.mem_bot] at this
    exact this
  set A' : Subgroup (Multiplicative (Vt 4)) := V₂.map φ₁ with hA'
  set B' : Subgroup (Multiplicative (Vt 4)) := V₂.map φ₂ with hB'
  have hcardA : Nat.card ↥A' = 2 ^ 2 := by
    have : Nat.card ↥A' = Nat.card ↥V₂ := by
      symm
      refine Nat.card_congr (Equiv.ofBijective
        (fun x : ↥V₂ => (⟨φ₁ x, ⟨x, x.2, rfl⟩⟩ : ↥A')) ⟨?_, ?_⟩)
      · intro x y hxy
        have h5 : φ₁ x = φ₁ y := congrArg Subtype.val hxy
        have h6 : φ₁ ((x : V) * (y : V)⁻¹) = 1 := by
          rw [map_mul, map_inv, h5]
          exact mul_inv_cancel _
        have h7 := hφ₁ker _ (V₂.mul_mem x.2 (V₂.inv_mem y.2)) h6
        exact Subtype.ext (mul_inv_eq_one.1 h7)
      · rintro ⟨_, ⟨x, hx, rfl⟩⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [this, hV₂]
    norm_num
  have hcardB : Nat.card ↥B' ≤ 4 := (card_map_le' φ₂ V₂).trans hV₂.le
  have hA'inv : SInvG (Ut 4) A' := by
    intro g hg x hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨ρ g v, hinv g hg v hv, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hφ₁eq, toAdd_ofAdd]
  have hA'eq : A' = Yk 4 2 := eq_Yk_of_Ut_invariant hA'inv hcardA
  have hB'inv : ∀ (j : Fin 4) (hj : j ≠ 0), ∀ x ∈ B',
      Multiplicative.ofAdd (mat (deltaSL (tv j hj)) *ᵥ Multiplicative.toAdd x) ∈ B' := by
    intro j hj x hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨ρ (tv j hj) v, hinv _ (tv_mem_Ut j hj) v hv, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hφ₂eq, toAdd_ofAdd]
  have hB0 : ∀ x ∈ B', Multiplicative.toAdd x 0 = 0 := by
    intro x hx
    by_contra hx0
    have hx1 : Multiplicative.toAdd x 0 = 1 := by
      revert hx0
      generalize Multiplicative.toAdd x 0 = c
      revert c
      decide
    have he : ∀ (j : Fin 4) (hj : j ≠ 0),
        Multiplicative.ofAdd (Pi.single j (1 : ZMod 2) : Vt 4) ∈ B' := by
      intro j hj
      have h3 := hB'inv j hj x hx
      rw [delta_tv_mulVec, hx1] at h3
      have h4 := B'.mul_mem hx h3
      have h5 : x * Multiplicative.ofAdd (Multiplicative.toAdd x + Pi.single j 1) =
          Multiplicative.ofAdd (Pi.single j (1 : ZMod 2) : Vt 4) := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
        funext i
        have key : ∀ a b : ZMod 2, a + (a + b) = b := by decide
        exact key _ _
      rw [h5] at h4
      exact h4
    let vs : Fin 5 → Vt 4 := ![0, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1,
      Pi.single 1 1 + Pi.single 2 1]
    have hvs : Function.Injective vs := by decide +kernel
    have hmem : ∀ i, Multiplicative.ofAdd (vs i) ∈ B' := by
      intro i
      fin_cases i
      · exact B'.one_mem
      · exact he 1 (by decide)
      · exact he 2 (by decide)
      · exact he 3 (by decide)
      · exact B'.mul_mem (he 1 (by decide)) (he 2 (by decide))
    have hg : Function.Injective (fun i : Fin 5 => (⟨Multiplicative.ofAdd (vs i), hmem i⟩ : ↥B')) := by
      intro i j hij
      exact hvs (Multiplicative.ofAdd.injective (congrArg Subtype.val hij))
    have h6 := Nat.card_le_card_of_injective _ hg
    rw [Nat.card_fin] at h6
    omega
  have he1 : Multiplicative.ofAdd (Pi.single 1 (1 : ZMod 2) : Vt 4) ∈ A' := by
    rw [hA'eq, mem_Yk]
    intro j hj
    rw [toAdd_ofAdd]
    have hj1 : j ≠ 1 := by
      intro h
      subst h
      exact absurd hj (by decide)
    simp [hj1]
  obtain ⟨v, hv, hvφ⟩ := Subgroup.mem_map.1 he1
  have htU : tv 1 (by decide) ∈ Ut 4 := tv_mem_Ut 1 (by decide)
  have hv'₂ : ρ (tv 1 (by decide)) v ∈ V₂ := hinv _ htU v hv
  have hφ₁v' : Multiplicative.toAdd (φ₁ (ρ (tv 1 (by decide)) v)) =
      Pi.single 1 1 + Pi.single 0 1 := by
    rw [hφ₁eq, hvφ, toAdd_ofAdd, tv_mulVec]
    simp
  have hφ₂v' : φ₂ (ρ (tv 1 (by decide)) v) = φ₂ v := by
    have hmem : φ₂ v ∈ B' := Subgroup.mem_map_of_mem _ hv
    apply Multiplicative.toAdd.injective
    rw [hφ₂eq, delta_tv_mulVec, hB0 _ hmem]
    simp
  set v' := ρ (tv 1 (by decide)) v with hv'
  have hker : φ₂ (v' * v⁻¹) = 1 := by
    rw [map_mul, map_inv, hφ₂v']
    exact mul_inv_cancel _
  have hker2 : q (v' * v⁻¹) = 1 := by
    have : p₂ (v' * v⁻¹) = 1 := C₂.β.injective (hker.trans (map_one C₂.β).symm)
    exact congrArg Subtype.val this
  have hU1 : v' * v⁻¹ ∈ U₁ := by
    have h8 : v' * v⁻¹ = p (v' * v⁻¹) := by
      have := hpq (v' * v⁻¹)
      rw [hker2, mul_one] at this
      exact this
    rw [h8]
    exact hp1 _
  have hmemV : v' * v⁻¹ ∈ V₂ ⊓ U₁ := ⟨V₂.mul_mem hv'₂ (V₂.inv_mem hv), hU1⟩
  rw [h1, Subgroup.mem_bot] at hmemV
  have hv'v : v' = v := mul_inv_eq_one.1 hmemV
  have h9 : φ₁ v' = φ₁ v := by rw [hv'v]
  have h10 := congrArg Multiplicative.toAdd h9
  rw [hφ₁v', hvφ, toAdd_ofAdd] at h10
  have h11 := congrFun h10 0
  simp at h11

end CaseB

section Final

variable {V : Type} [CommGroup V]

theorem exists_conj_unitri [Finite V] {X S K : Subgroup (MulAut V)} (hKX : K ≤ X)
    (hnorm : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hS : IsSylowTwoOf S X)
    (hKcard : Nat.card ↥K = 20160) {π : ↥(StatedSL 4 (ZMod 2)) →* ↥K} (hπ : Function.Surjective π) :
    ∃ g : SLt 4, ∀ h ∈ Ut 4, rhoOf π (g * h * g⁻¹) ∈ S := by
  have hbij : Function.Bijective π := by
    rw [Nat.bijective_iff_surjective_and_card]
    exact ⟨hπ, by rw [hKcard]; exact card_statedSL_four_zmod1527d⟩
  let ε := specialLinearGroupEquivStatedSL 4 (ZMod 2)
  let e₀ : ↥K ≃* SLt 4 := (MulEquiv.ofBijective π hbij).symm.trans ε.symm
  have hS0 : IsSylowTwoOf (S ⊓ K) K :=
    B6.isSylowTwoOf_inf_normal hS hKX (FLc.le_normalizer_of_conj_mem hnorm)
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hS0
  let Q : Sylow 2 (SLt 4) := Sylow.mapSurjective (f := e₀.toMonoidHom) e₀.surjective P
  have hQ : (Q : Subgroup (SLt 4)) = (P : Subgroup ↥K).map e₀.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e₀.toMonoidHom) e₀.surjective P
  obtain ⟨g, hg⟩ := exists_conj_eq_unitriangular (by norm_num : 1 ≤ 4) Q
  refine ⟨g, fun h hh => ?_⟩
  have h1 : g * h * g⁻¹ ∈ (Q : Subgroup (SLt 4)) := by
    rw [hg]
    exact ⟨h, hh, by simp [MulAut.conj_apply]⟩
  rw [hQ] at h1
  obtain ⟨x, hxP, hx⟩ := Subgroup.mem_map.1 h1
  have hx1 : (x : MulAut V) ∈ S ⊓ K := by
    have : x ∈ (P : Subgroup ↥K) := hxP
    rw [hP, Subgroup.mem_subgroupOf] at this
    exact this
  have hx2 : x = π (ε (g * h * g⁻¹)) := by
    have hx' : e₀ x = g * h * g⁻¹ := hx
    have h5 := congrArg e₀.symm hx'
    rw [MulEquiv.symm_apply_apply] at h5
    exact h5
  rw [rhoOf_apply, ← hx2]
  exact hx1.1

theorem conj_dual_rel (ρ₁ : SLt 4 →* MulAut V) (g : SLt 4) (h : SLt 4) :
    (((ρ₁.comp deltaSL).comp (MulAut.conj (deltaSL g)).toMonoidHom) h) =
      ((ρ₁.comp (MulAut.conj g).toMonoidHom) (deltaSL h)) := by
  have e : deltaSL (deltaSL g * h * (deltaSL g)⁻¹) = g * deltaSL h * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, deltaSL_deltaSL]
  show ρ₁ (deltaSL (deltaSL g * h * (deltaSL g)⁻¹)) = ρ₁ (g * deltaSL h * g⁻¹)
  rw [e]

theorem comp_delta_mem {ρ : SLt 4 →* MulAut V} {K : Subgroup (MulAut V)} (h : ∀ g, ρ g ∈ K) :
    ∀ g, (ρ.comp deltaSL) g ∈ K := fun g => h (deltaSL g)

theorem comp_delta_surj {ρ : SLt 4 →* MulAut V} {K : Subgroup (MulAut V)}
    (hρs : ∀ k ∈ K, ∃ g, ρ g = k) : ∀ k ∈ K, ∃ g, (ρ.comp deltaSL) g = k := by
  intro k hk
  obtain ⟨g, hg⟩ := hρs k hk
  refine ⟨deltaSL g, ?_⟩
  show ρ (deltaSL (deltaSL g)) = k
  rw [deltaSL_deltaSL, hg]

theorem not_sumNatDual [Finite V] {X S : Subgroup (MulAut V)} {V₂ : Subgroup V} {y : MulAut V}
    (θ : ↥X ≃* Equiv.Perm (Fin 8)) (hS : IsSylowTwoOf S X) (hV₂ : Nat.card ↥V₂ = 4)
    (hSV₂ : ∀ s ∈ S, ∀ v ∈ V₂, s v ∈ V₂) (hy : y ∈ ⁅X, X⁆) (hyV₂ : ∀ v ∈ V₂, y v ∈ V₂)
    (hyfix : ∀ v ∈ V₂, y v = v → v = 1) : ¬ SumNatDual ⁅X, X⁆ ⊤ 4 := by
  rintro ⟨-, π, U₁, U₂, hdir, h₁, h₂⟩
  obtain ⟨s, hsS, hsK⟩ := exists_sylow_not_comm θ hS
  have hKX : ⁅X, X⁆ ≤ X := commutator_le_self X
  have hnorm : ∀ x ∈ X, ∀ k ∈ ⁅X, X⁆, x * k * x⁻¹ ∈ ⁅X, X⁆ := fun x hx k hk => comm_conj_mem hx hk
  have hcent := centralizer_comm_trivial θ
  have hsX : s ∈ X := hS.1 hsS
  have hπ : Function.Surjective π := h₁.1
  obtain ⟨C₁⟩ := natCoord_of_realizes h₁
  obtain ⟨C₂⟩ := natCoord_of_dual h₂
  have hρ₁K : ∀ g, rhoOf π g ∈ ⁅X, X⁆ := rhoOf_mem π
  have hρ₁s : ∀ k ∈ ⁅X, X⁆, ∃ g, rhoOf π g = k := rhoOf_surj hπ
  have hρ₂K : ∀ g, ((rhoOf π).comp deltaSL) g ∈ ⁅X, X⁆ := comp_delta_mem hρ₁K
  have hρ₂s : ∀ k ∈ ⁅X, X⁆, ∃ g, ((rhoOf π).comp deltaSL) g = k := comp_delta_surj hρ₁s
  have hU₁ : ∀ k ∈ ⁅X, X⁆, ∀ u ∈ U₁, k u ∈ U₁ := by
    intro k hk u hu
    obtain ⟨g, rfl⟩ := hρ₁s k hk
    exact C₁.inv g u hu
  have hU₂ : ∀ k ∈ ⁅X, X⁆, ∀ u ∈ U₂, k u ∈ U₂ := by
    intro k hk u hu
    obtain ⟨g, rfl⟩ := hρ₂s k hk
    exact C₂.inv g u hu
  have hV₂ne : V₂ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hV₂
    omega
  have hsV₂ : ∀ v ∈ V₂, s v ∈ V₂ := hSV₂ s hsS
  rcases inf_eq_bot_or_le hV₂ (hU₁ y hy) hyV₂ hyfix with h1 | h1
  · rcases inf_eq_bot_or_le hV₂ (hU₂ y hy) hyV₂ hyfix with h2 | h2
    ·
      obtain ⟨g, hg⟩ := exists_conj_unitri hKX hnorm hS (card_comm_s8 θ) hπ
      exact false_of_graph hdir (C₁.conj g) (conj_dual_rel (rhoOf π) g) (C₂.conj (deltaSL g)) hV₂
        (fun h hh v hv => hSV₂ _ (hg h hh) v hv) h1 h2
    · exact false_of_le_natural hKX hnorm hcent hρ₂K hρ₂s C₂ hsX hsK hsV₂ h2 hV₂ne
  · exact false_of_le_natural hKX hnorm hcent hρ₁K hρ₁s C₁ hsX hsK hsV₂ h1 hV₂ne

theorem excl34 [Finite V] {X S : Subgroup (MulAut V)} {V₂ : Subgroup V} {y : MulAut V}
    (θ : ↥X ≃* Equiv.Perm (Fin 8)) (hS : IsSylowTwoOf S X) (hV₂ : Nat.card ↥V₂ = 4)
    (hSV₂ : ∀ s ∈ S, ∀ v ∈ V₂, s v ∈ V₂) (hy : y ∈ ⁅X, X⁆) (hyV₂ : ∀ v ∈ V₂, y v ∈ V₂)
    (hyfix : ∀ v ∈ V₂, y v = v → v = 1) :
    ¬ SumNatDual ⁅X, X⁆ ⊤ 4 ∧ ¬ ∃ k : ℕ, 1 ≤ k ∧ k ≤ 3 ∧
      DirectSumOfCopies ⁅X, X⁆ ⊤ ⊥ (FFModel.nat (StatedSL 4 (ZMod 2))) k := by
  refine ⟨not_sumNatDual θ hS hV₂ hSV₂ hy hyV₂ hyfix, ?_⟩
  rintro ⟨k, hk1, -, hdir⟩
  obtain ⟨s, hsS, hsK⟩ := exists_sylow_not_comm θ hS
  exact not_directSum_nat (fun x hx k hk => comm_conj_mem hx hk) (centralizer_comm_trivial θ)
    (hS.1 hsS) hsK k hk1 hdir

end Final

end CoordLemmas

end Coord

end LRed4

end CFSG.Quasithin
