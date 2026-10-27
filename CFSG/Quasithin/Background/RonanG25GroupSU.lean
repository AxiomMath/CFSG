module

public import CFSG.Quasithin.Background.RonanG25GroupV

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

section QvHom

noncomputable def ronanQvHom (F : Type) [Field F] : Multiplicative (Fin 2 → F) →* SL(3, F) where
  toFun q := tqv (Multiplicative.toAdd q)
  map_one' := tq_zero
  map_mul' a b := tq_add (Multiplicative.toAdd a 0) (Multiplicative.toAdd a 1)
    (Multiplicative.toAdd b 0) (Multiplicative.toAdd b 1)

theorem ronanQvHom_injective (F : Type) [Field F] : Function.Injective (ronanQvHom F) := by
  intro a b hab
  have h1 : tq (Multiplicative.toAdd a 0) (Multiplicative.toAdd a 1) =
      tq (Multiplicative.toAdd b 0) (Multiplicative.toAdd b 1) := hab
  obtain ⟨h0, h1'⟩ := tq_injective h1
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · exact h0
  · exact h1'

theorem ronanQvHom_range (F : Type) [Field F] : (ronanQvHom F).range = Qv (vE F 0) := by
  ext A
  rw [MonoidHom.mem_range, mem_Qv_e0]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨Multiplicative.toAdd q 0, Multiplicative.toAdd q 1, rfl⟩
  · rintro ⟨b, c, rfl⟩
    exact ⟨Multiplicative.ofAdd ![b, c], rfl⟩

end QvHom

section GroupSU

variable {G : Type} [Group G] [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G}

theorem chain_S_SU_group (St : L3Setting n V V₁ L T H) {g h : G} (hsub : SubFacts V L H g h)
    {ord : Bool} :
    ChainCounts (GaloisField 2 n) (lOne L V₁) ord (gS V H L) (gS V H L ⊔ conjClosure V H) 1 0 := by
  have hLI : L ≤ L ⊔ conjClosure V H := le_sup_left
  have hUI : conjClosure V H ≤ L ⊔ conjClosure V H := le_sup_right
  have hSB : gS V H L ≤ gS V H L ⊔ conjClosure V H := le_sup_left
  have hUB : conjClosure V H ≤ gS V H L ⊔ conjClosure V H := le_sup_right
  have hlL : lOne L V₁ ≤ L := lOne_le_L
  have hpc : pCoreOf 2 (L ⊔ conjClosure V H) ≤ L ⊔ conjClosure V H :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hBI : gS V H L ⊔ conjClosure V H ≤ L ⊔ conjClosure V H := sup_le hpc hUI
  have hI : ∀ y : ↥(gS V H L ⊔ conjClosure V H), (y : G) ∈ L ⊔ conjClosure V H :=
    fun y => hBI y.2
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ↥(gS V H L ⊔ conjClosure V H) →* SL(3, GaloisField 2 n),
      ∀ y, Ψ y = St.Phi ⟨(y : G), hI y⟩ :=
    ⟨St.Phi.comp (Subgroup.inclusion hBI), fun y => rfl⟩
  have hΨQ : ∀ y, Ψ y ∈ Qv (vE (GaloisField 2 n) 0) := by
    have hle : gS V H L ⊔ conjClosure V H ≤
        ((Qv (vE (GaloisField 2 n) 0)).comap St.Phi).map (L ⊔ conjClosure V H).subtype := by
      refine sup_le (fun s hs => ?_) (fun u hu => ?_)
      · have hsI : s ∈ L ⊔ conjClosure V H := hpc hs
        refine Subgroup.mem_map.2 ⟨⟨s, hsI⟩, ?_, rfl⟩
        have h1 : St.Phi ⟨s, hsI⟩ = 1 := (St.Phi_eq_one_iff_mem_S ⟨s, hsI⟩).2 hs
        rw [Subgroup.mem_comap, h1]
        exact (Qv (vE (GaloisField 2 n) 0)).one_mem
      · have huI : u ∈ L ⊔ conjClosure V H := hUI hu
        refine Subgroup.mem_map.2 ⟨⟨u, huI⟩, ?_, rfl⟩
        rw [Subgroup.mem_comap]
        exact St.betaU_mem_Qv ⟨u, hu⟩
    intro y
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 (hle y.2)
    have hzeq : z = ⟨(y : G), hI y⟩ := Subtype.ext hzy
    rw [hΨ y, ← hzeq]
    exact Subgroup.mem_comap.1 hz
  have hΨr : ∀ y, Ψ y ∈ (ronanQvHom (GaloisField 2 n)).range := fun y => by
    rw [ronanQvHom_range]
    exact hΨQ y
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(gS V H L ⊔ conjClosure V H) →* Multiplicative (Fin 2 → GaloisField 2 n),
      ∀ y, ronanQvHom (GaloisField 2 n) (φ y) = Ψ y :=
    ⟨(MonoidHom.ofInjective (ronanQvHom_injective (GaloisField 2 n))).symm.toMonoidHom.comp
        (Ψ.codRestrict (ronanQvHom (GaloisField 2 n)).range hΨr),
      fun y => MonoidHom.apply_ofInjective_symm (ronanQvHom_injective (GaloisField 2 n)) _⟩
  have hker : ∀ z : ↥(gS V H L ⊔ conjClosure V H), φ z = 1 ↔ (z : G) ∈ gS V H L := by
    intro z
    have h1 : φ z = 1 ↔ Ψ z = 1 := by
      constructor
      · intro h
        rw [← hφ z, h, map_one]
      · intro h
        apply ronanQvHom_injective (GaloisField 2 n)
        rw [map_one, hφ z, h]
    rw [h1, hΨ z]
    exact St.Phi_eq_one_iff_mem_S ⟨(z : G), hI z⟩
  have hpreBot : pre (gS V H L ⊔ conjClosure V H) φ ⊥ = gS V H L := by
    ext y
    rw [mem_pre]
    constructor
    · rintro ⟨hyB, h⟩
      rw [AddSubgroup.mem_bot, toAdd_eq_zero] at h
      exact (hker ⟨y, hyB⟩).1 h
    · intro hy
      have hyB : y ∈ gS V H L ⊔ conjClosure V H := hSB hy
      refine ⟨hyB, ?_⟩
      rw [AddSubgroup.mem_bot, toAdd_eq_zero]
      exact (hker ⟨y, hyB⟩).2 hy
  have hpreTop : pre (gS V H L ⊔ conjClosure V H) φ ⊤ = gS V H L ⊔ conjClosure V H := by
    ext y
    rw [mem_pre]
    constructor
    · rintro ⟨hyB, _⟩
      exact hyB
    · intro hyB
      exact ⟨hyB, AddSubgroup.mem_top _⟩
  have hsurj : ∀ e : Fin 2 → GaloisField 2 n, ∃ y : ↥(gS V H L ⊔ conjClosure V H),
      φ y = Multiplicative.ofAdd e := by
    intro e
    have hmem : tqv e ∈ St.Ubar := by
      rw [St.Ubar_eq_Qv]
      exact tq_mem_Qv (e 0) (e 1)
    obtain ⟨u, hu⟩ := hmem
    refine ⟨⟨(u : G), hUB u.2⟩, ?_⟩
    apply ronanQvHom_injective (GaloisField 2 n)
    rw [hφ, hΨ]
    exact hu
  have hnorm : ∀ x ∈ lOne L V₁, ∀ y ∈ gS V H L ⊔ conjClosure V H,
      x * y * x⁻¹ ∈ gS V H L ⊔ conjClosure V H := by
    intro x hx
    have hxLI : x ∈ L ⊔ conjClosure V H := hLI (hlL hx)
    have hxH : x ∈ H := St.hyp.base.lOne_sup_le ((le_sup_left : lOne L V₁ ≤ lOne L V₁ ⊔ T) hx)
    have hS : ∀ s ∈ gS V H L, x * s * x⁻¹ ∈ gS V H L := fun s hs =>
      (Subgroup.mem_normalizer_iff.1 (hsub.I_S hxLI) s).1 hs
    have hU : ∀ u ∈ conjClosure V H, x * u * x⁻¹ ∈ conjClosure V H := fun u hu =>
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure V H hxH) u).1 hu
    have hK : gS V H L ⊔ conjClosure V H ≤
        (gS V H L ⊔ conjClosure V H).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro s hs
        rw [Subgroup.mem_comap]
        show x * s * x⁻¹ ∈ gS V H L ⊔ conjClosure V H
        exact hSB (hS s hs)
      · intro u hu
        rw [Subgroup.mem_comap]
        show x * u * x⁻¹ ∈ gS V H L ⊔ conjClosure V H
        exact hUB (hU u hu)
    intro y hy
    exact Subgroup.mem_comap.1 (hK hy)
  have hE : Equivariant (lOne L V₁) (gS V H L ⊔ conjClosure V H) φ (actU (rho St.D)) := by
    refine ⟨hnorm, ?_⟩
    intro x y y' hyy'
    have hxLI : (x : G) ∈ L ⊔ conjClosure V H := hLI (hlL x.2)
    have hPhix : St.Phi ⟨(x : G), hxLI⟩ = rho St.D x := St.Phi_of_L ⟨(x : G), hlL x.2⟩
    have hconj : Ψ y' = rho St.D x * Ψ y * (rho St.D x)⁻¹ := by
      have e : (⟨(y' : G), hI y'⟩ : ↥(L ⊔ conjClosure V H)) =
          ⟨(x : G), hxLI⟩ * ⟨(y : G), hI y⟩ * ⟨(x : G), hxLI⟩⁻¹ := Subtype.ext hyy'.symm
      rw [hΨ y', hΨ y, e, map_mul, map_mul, map_inv, hPhix]
    apply ronanQvHom_injective (GaloisField 2 n)
    rw [hφ y', hconj, ← hφ y]
    exact conj_tqv ((l1Rep St).stab x) (Multiplicative.toAdd (φ y))
  have hN : ∀ e : Fin 2 → GaloisField 2 n,
      e ∈ (⊤ : AddSubgroup (Fin 2 → GaloisField 2 n)) ↔ ∃ y, φ y = Multiplicative.ofAdd e :=
    fun e => ⟨fun _ => hsurj e, fun _ => AddSubgroup.mem_top _⟩
  have hchain : ChainCounts (GaloisField 2 n) (lOne L V₁) ord
      (pre (gS V H L ⊔ conjClosure V H) φ ⊥) (pre (gS V H L ⊔ conjClosure V H) φ ⊤) 1 0 :=
    ModChain.transport hN hE (chain_U (l1Rep St)) le_top
  rw [hpreBot, hpreTop] at hchain
  exact hchain

end GroupSU

end CFSG.Quasithin.RonanG25
