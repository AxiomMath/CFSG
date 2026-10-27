module

public import CFSG.Quasithin.Vol2.Ch3Sec3A6Cocycle
public import Certificates.Certificate7093

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Heart

variable {m : ℕ}

theorem heartAct_mul (σ τ : Equiv.Perm (Fin m)) (y : AltHeart m) :
    heartAct m (σ * τ) y = heartAct m σ (heartAct m τ y) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rfl

theorem heartAct_one (y : AltHeart m) : heartAct m 1 y = y := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rfl

end Heart

namespace A6Coc

theorem rels_ab : aP ^ 3 = 1 ∧ fixCount aP = 4 ∧ bP ^ 5 = 1 ∧ (aP * bP) ^ 4 = 1 ∧
    (aP ^ 2 * bP ^ 2) ^ 3 = 1 := by
  decide +kernel

@[expose] def e₀ : Vec4 := ![1, 0, 0, 0]

@[expose] def gB : Fin 4 → Equiv.Perm (Fin 6) := ![1, aP, bP * aP, bP * bP * aP]

theorem schurCheck : ∀ w : Vec4, act (aP * bP) w = w → w = 0 ∨ w = e₀ := by decide +kernel

theorem basisCheck : act (aP * bP) e₀ = e₀ ∧ ∀ i : Fin 4, act (gB i) e₀ = Pi.single i 1 := by
  decide +kernel

theorem e₀_ne_zero : e₀ ≠ 0 := by decide

theorem schur (M : Vec4 →+ Vec4) (ha : ∀ v, M (act aP v) = act aP (M v))
    (hb : ∀ v, M (act bP v) = act bP (M v)) : M = 0 ∨ M = AddMonoidHom.id Vec4 := by
  have hab : ∀ v, M (act (aP * bP) v) = act (aP * bP) (M v) := fun v => by
    rw [act_mul, ha, hb, act_mul]
  have hg : ∀ i : Fin 4, ∀ v, M (act (gB i) v) = act (gB i) (M v) := by
    intro i v
    fin_cases i
    · show M (act 1 v) = act 1 (M v)
      rw [act_one, act_one]
    · exact ha v
    · show M (act (bP * aP) v) = act (bP * aP) (M v)
      rw [act_mul, hb, ha, act_mul]
    · show M (act (bP * bP * aP) v) = act (bP * bP * aP) (M v)
      rw [act_mul, act_mul, hb, hb, ha, act_mul, act_mul]
  obtain ⟨h1, h2⟩ := basisCheck
  have hM0 : M e₀ = 0 ∨ M e₀ = e₀ := schurCheck (M e₀) (by rw [← hab, h1])
  have hsingle : ∀ i : Fin 4, M (Pi.single i 1) = act (gB i) (M e₀) := fun i => by
    rw [← h2 i, hg]
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hM0 with h | h
  · left
    refine AddMonoidHom.functions_ext _ _ _ fun i x => ?_
    rcases h01 x with rfl | rfl
    · rw [Pi.single_zero, map_zero, map_zero]
    · rw [hsingle, h, act_zero]
      rfl
  · right
    refine AddMonoidHom.functions_ext _ _ _ fun i x => ?_
    rcases h01 x with rfl | rfl
    · rw [Pi.single_zero, map_zero, map_zero]
    · rw [hsingle, h, h2]
      rfl

@[expose] def epsInvHom : Vec4 →+ AltHeart 6 where
  toFun := epsInv
  map_zero' := by
    show (QuotientAddGroup.mk ⟨sec 0, sec_mem 0⟩ : AltHeart 6) = 0
    have e : (⟨sec 0, sec_mem 0⟩ : ↥(evenWeight 6)) = 0 := Subtype.ext sec_zero
    rw [e]
    rfl
  map_add' u v := by
    show (QuotientAddGroup.mk ⟨sec (u + v), sec_mem (u + v)⟩ : AltHeart 6) =
      QuotientAddGroup.mk ⟨sec u, sec_mem u⟩ + QuotientAddGroup.mk ⟨sec v, sec_mem v⟩
    have e : (⟨sec (u + v), sec_mem (u + v)⟩ : ↥(evenWeight 6)) =
        ⟨sec u, sec_mem u⟩ + ⟨sec v, sec_mem v⟩ := Subtype.ext (sec_add u v)
    rw [e]
    rfl

theorem epsInv_eps (y : AltHeart 6) : epsInv (eps y) = y :=
  eps_injective (eps_epsInv (eps y))

theorem fixCount_eq (τ : Equiv.Perm (Fin 6)) :
    fixCount τ = Nat.card {y : AltHeart 6 // heartAct 6 τ y = y} := by
  rw [fixCount, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  let e : {v : Vec4 // act τ v = v} ≃ {y : AltHeart 6 // heartAct 6 τ y = y} :=
    { toFun := fun v => ⟨epsInv v.1, eps_injective (by rw [eps_heartAct, eps_epsInv]; exact v.2)⟩
      invFun := fun y => ⟨eps y.1, by rw [← eps_heartAct, y.2]⟩
      left_inv := fun v => Subtype.ext (eps_epsInv v.1)
      right_inv := fun y => Subtype.ext (epsInv_eps y.1) }
  exact Nat.card_congr e

end A6Coc

namespace A6Trans

open A6Coc

variable {G : Type} [Group G] {L : Subgroup G}

theorem exists_perm {α : ↥L →* alternatingGroup (Fin 6)}
    {β : ↥(blockU L) →* Multiplicative (AltHeart 6)}
    (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (hβs : Function.Surjective β) (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight 6 (α ℓ : Equiv.Perm (Fin 6)) x) : AltHeart 6) =
          Multiplicative.toAdd (β v))
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ∃ σ : Equiv.Perm (Fin 6),
      (∀ ℓ ℓ' : ↥L, (ℓ' : G) = g * ℓ * g⁻¹ →
        (α ℓ' : Equiv.Perm (Fin 6)) = σ * (α ℓ : Equiv.Perm (Fin 6)) * σ⁻¹) ∧
      ∀ u u' : ↥(blockU L), (u' : G) = g * u * g⁻¹ →
        Multiplicative.toAdd (β u') = heartAct 6 σ (Multiplicative.toAdd (β u)) := by
  have hgi : g⁻¹ ∈ Subgroup.normalizer (L : Set G) := inv_mem hg
  have hgQ := C1.mem_normalizer_blockQ hg
  have hgU := C1.mem_normalizer_blockU hg
  have hgZ := C1.mem_normalizer_blockZ hg
  have hgiZ := C1.mem_normalizer_blockZ hgi
  let cL : ↥L →* ↥L :=
    { toFun := fun ℓ => ⟨g * ℓ * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg ℓ).mp ℓ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let cU : ↥(blockU L) →* ↥(blockU L) :=
    { toFun := fun u => ⟨g * u * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgU u).mp u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcL : ∀ ℓ : ↥L, ((cL ℓ : ↥L) : G) = g * ℓ * g⁻¹ := fun _ => rfl
  have hcU : ∀ u : ↥(blockU L), ((cU u : ↥(blockU L)) : G) = g * u * g⁻¹ := fun _ => rfl
  have hdepL : ∀ ℓ ℓ' : ↥L, α ℓ = α ℓ' → α (cL ℓ) = α (cL ℓ') := by
    intro ℓ ℓ' he
    have hk : ℓ'⁻¹ * ℓ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    rw [hαk, Lem3328.mem_pCore_iff] at hk
    have hk' : cL (ℓ'⁻¹ * ℓ) ∈ α.ker := by
      rw [hαk, Lem3328.mem_pCore_iff, hcL]
      exact (Subgroup.mem_normalizer_iff.mp hgQ _).mp hk
    rw [map_mul, map_inv, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk'
    exact hk'.symm
  obtain ⟨ψ, hψα⟩ : ∃ ψ : A6Coc.Γ →* A6Coc.Γ, ∀ ℓ : ↥L, ψ (α ℓ) = α (cL ℓ) := by
    refine ⟨MonoidHom.mk' (fun x => α (cL (Function.surjInv hαs x))) ?_,
      fun ℓ => hdepL _ _ (Function.surjInv_eq hαs (α ℓ))⟩
    intro x y
    obtain ⟨ℓ, rfl⟩ := hαs x
    obtain ⟨ℓ', rfl⟩ := hαs y
    have h1 := hdepL _ _ (Function.surjInv_eq hαs (α ℓ))
    have h2 := hdepL _ _ (Function.surjInv_eq hαs (α ℓ'))
    have h3 : α (cL (Function.surjInv hαs (α ℓ * α ℓ'))) = α (cL (ℓ * ℓ')) :=
      hdepL _ _ (by rw [Function.surjInv_eq hαs, map_mul])
    show α (cL (Function.surjInv hαs (α ℓ * α ℓ'))) =
      α (cL (Function.surjInv hαs (α ℓ))) * α (cL (Function.surjInv hαs (α ℓ')))
    rw [h1, h2, h3, map_mul, map_mul]
  have hdepU : ∀ u u' : ↥(blockU L), β u = β u' → β (cU u) = β (cU u') := by
    intro u u' he
    have hk : u'⁻¹ * u ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    rw [hβk, Subgroup.mem_subgroupOf] at hk
    have hk' : cU (u'⁻¹ * u) ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf, hcU]
      exact (Subgroup.mem_normalizer_iff.mp hgZ _).mp hk
    rw [map_mul, map_inv, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk'
    exact hk'.symm
  obtain ⟨φ, hφβ⟩ : ∃ φ : AltHeart 6 →+ AltHeart 6, ∀ u : ↥(blockU L),
      φ (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (cU u)) := by
    let w : AltHeart 6 → ↥(blockU L) := fun y => Function.surjInv hβs (Multiplicative.ofAdd y)
    have hw : ∀ y, β (w y) = Multiplicative.ofAdd y := fun y => Function.surjInv_eq hβs _
    refine ⟨{ toFun := fun y => Multiplicative.toAdd (β (cU (w y))),
              map_zero' := ?_, map_add' := ?_ }, fun u => ?_⟩
    · have h1 : β (cU (w 0)) = β (cU 1) := hdepU _ _ (by rw [hw, map_one]; rfl)
      show Multiplicative.toAdd (β (cU (w 0))) = 0
      rw [h1, map_one, map_one]
      rfl
    · intro y y'
      have h1 : β (cU (w (y + y'))) = β (cU (w y * w y')) :=
        hdepU _ _ (by rw [hw, map_mul, hw, hw]; rfl)
      show Multiplicative.toAdd (β (cU (w (y + y')))) =
        Multiplicative.toAdd (β (cU (w y))) + Multiplicative.toAdd (β (cU (w y')))
      rw [h1, map_mul, map_mul, toAdd_mul]
    · show Multiplicative.toAdd (β (cU (w (Multiplicative.toAdd (β u))))) = _
      rw [hdepU _ u (by rw [hw, ofAdd_toAdd])]
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd y)
    have e1 : y = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    rw [e1, hφβ] at hy
    have hy' : cU u ∈ β.ker := by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective hy
    rw [hβk, Subgroup.mem_subgroupOf, hcU] at hy'
    have hk2 : g⁻¹ * (g * (u : G) * g⁻¹) * g⁻¹⁻¹ ∈ blockZ L :=
      (Subgroup.mem_normalizer_iff.mp hgiZ _).mp hy'
    have e3 : g⁻¹ * (g * (u : G) * g⁻¹) * g⁻¹⁻¹ = u := by group
    rw [e3] at hk2
    have hk3 : u ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf]
      exact hk2
    rw [MonoidHom.mem_ker] at hk3
    rw [e1, hk3]
    rfl
  have hφsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hφinj
  have hφψ : ∀ (x : A6Coc.Γ) (y : AltHeart 6),
      φ (heartAct 6 (x : Equiv.Perm (Fin 6)) y) =
        heartAct 6 (ψ x : Equiv.Perm (Fin 6)) (φ y) := by
    intro x y
    obtain ⟨ℓ, rfl⟩ := hαs x
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd y)
    have e1 : y = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    have hw : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (Subgroup.le_normalizer ℓ.2))
        _).mp u.2
    have h1 := heartAct_eq_of_equivariant hβe ℓ u ⟨_, hw⟩ rfl
    have hw' : ((cL ℓ : ↥L) : G) * (cU u : G) * ((cL ℓ : ↥L) : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU
        (Subgroup.le_normalizer (cL ℓ).2)) _).mp (cU u).2
    have h2 := heartAct_eq_of_equivariant hβe (cL ℓ) (cU u) ⟨_, hw'⟩ rfl
    have e2 : cU ⟨_, hw⟩ = ⟨_, hw'⟩ := Subtype.ext (by
      show g * ((ℓ : G) * u * (ℓ : G)⁻¹) * g⁻¹ =
        g * ℓ * g⁻¹ * (g * u * g⁻¹) * (g * ℓ * g⁻¹)⁻¹
      group)
    rw [e1, ← h1, hφβ, e2, h2, hψα, hφβ]
  have hfix : ∀ x : A6Coc.Γ, fixCount (ψ x : Equiv.Perm (Fin 6)) =
      fixCount (x : Equiv.Perm (Fin 6)) := by
    intro x
    rw [fixCount_eq, fixCount_eq]
    let e : {y : AltHeart 6 // heartAct 6 (x : Equiv.Perm (Fin 6)) y = y} ≃
        {y : AltHeart 6 // heartAct 6 (ψ x : Equiv.Perm (Fin 6)) y = y} :=
      { toFun := fun y => ⟨φ y.1, by rw [← hφψ, y.2]⟩
        invFun := fun z => ⟨Function.surjInv hφsurj z.1,
          hφinj (by rw [hφψ, Function.surjInv_eq hφsurj]; exact z.2)⟩
        left_inv := fun y => Subtype.ext (hφinj (Function.surjInv_eq hφsurj _))
        right_inv := fun z => Subtype.ext (Function.surjInv_eq hφsurj _) }
    exact (Nat.card_congr e).symm
  obtain ⟨ha3, hafix, hb5, hab4, hab3⟩ := rels_ab
  have hrel : ∀ (x : A6Coc.Γ) (n : ℕ), (x : Equiv.Perm (Fin 6)) ^ n = 1 →
      (ψ x : Equiv.Perm (Fin 6)) ^ n = 1 := by
    intro x n hx
    have hx' : x ^ n = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hx)
    rw [← Subgroup.coe_pow, ← map_pow, hx', map_one]
    rfl
  obtain ⟨σ, hσa, hσb⟩ := Certificates.certificate7093 (ψ aL) (ψ bL)
    ⟨hrel aL 3 ha3, by rw [hfix]; exact hafix, hrel bL 5 hb5,
      by
        have := hrel (aL * bL) 4 hab4
        rwa [map_mul, Subgroup.coe_mul] at this,
      by
        have := hrel (aL ^ 2 * bL ^ 2) 3
          (by rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]; exact hab3)
        rwa [map_mul, map_pow, map_pow, Subgroup.coe_mul, Subgroup.coe_pow,
          Subgroup.coe_pow] at this⟩
  have hψσ : ∀ x : A6Coc.Γ, (ψ x : Equiv.Perm (Fin 6)) = σ * x * σ⁻¹ := by
    have key : (alternatingGroup (Fin 6)).subtype.comp ψ =
        (MulAut.conj σ).toMonoidHom.comp (alternatingGroup (Fin 6)).subtype := by
      refine MonoidHom.eq_of_eqOn_dense closure_ab ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · show (ψ aL : Equiv.Perm (Fin 6)) = σ * aP * σ⁻¹
        exact hσa.symm
      · show (ψ bL : Equiv.Perm (Fin 6)) = σ * bP * σ⁻¹
        exact hσb.symm
    intro x
    exact DFunLike.congr_fun key x
  let χ : AltHeart 6 →+ AltHeart 6 := (heartAct 6 σ⁻¹).comp φ
  have hχ : ∀ (x : A6Coc.Γ) (y : AltHeart 6),
      χ (heartAct 6 (x : Equiv.Perm (Fin 6)) y) = heartAct 6 (x : Equiv.Perm (Fin 6)) (χ y) := by
    intro x y
    show heartAct 6 σ⁻¹ (φ (heartAct 6 (x : Equiv.Perm (Fin 6)) y)) =
      heartAct 6 (x : Equiv.Perm (Fin 6)) (heartAct 6 σ⁻¹ (φ y))
    rw [hφψ, hψσ, ← heartAct_mul, ← heartAct_mul,
      show σ⁻¹ * (σ * (x : Equiv.Perm (Fin 6)) * σ⁻¹) = (x : Equiv.Perm (Fin 6)) * σ⁻¹ by group]
  have hσχ : ∀ y, heartAct 6 σ (χ y) = φ y := by
    intro y
    show heartAct 6 σ (heartAct 6 σ⁻¹ (φ y)) = φ y
    rw [← heartAct_mul, mul_inv_cancel, heartAct_one]
  let M : Vec4 →+ Vec4 := eps.comp (χ.comp epsInvHom)
  have hMact : ∀ (x : A6Coc.Γ) (v : Vec4),
      M (act (x : Equiv.Perm (Fin 6)) v) = act (x : Equiv.Perm (Fin 6)) (M v) := by
    intro x v
    show eps (χ (epsInv (act x v))) = act x (eps (χ (epsInv v)))
    have e : epsInv (act (x : Equiv.Perm (Fin 6)) v) =
        heartAct 6 (x : Equiv.Perm (Fin 6)) (epsInv v) := by
      apply eps_injective
      rw [eps_epsInv, eps_heartAct, eps_epsInv]
    rw [e, hχ, eps_heartAct]
  rcases schur M (hMact aL) (hMact bL) with h0 | hid
  · exfalso
    have h1 : eps (χ (epsInv e₀)) = 0 := by
      have : M e₀ = 0 := by rw [h0]; rfl
      exact this
    have h2 : χ (epsInv e₀) = 0 := eps_injective (by rw [map_zero]; exact h1)
    have h3 : φ (epsInv e₀) = 0 := by rw [← hσχ, h2, map_zero]
    have h4 : epsInv e₀ = 0 := hφinj (by rw [h3, map_zero])
    have h5 := eps_epsInv e₀
    rw [h4, map_zero] at h5
    exact e₀_ne_zero h5.symm
  · have hφσ : ∀ y, φ y = heartAct 6 σ y := by
      intro y
      have h1 : eps (χ (epsInv (eps y))) = eps y := by
        have : M (eps y) = eps y := by rw [hid]; rfl
        exact this
      rw [epsInv_eps] at h1
      rw [← hσχ, eps_injective h1]
    refine ⟨σ, fun ℓ ℓ' hℓ => ?_, fun u u' hu => ?_⟩
    · have e : ℓ' = cL ℓ := Subtype.ext hℓ
      rw [e, ← hψα, hψσ]
    · have e : u' = cU u := Subtype.ext hu
      rw [e, ← hφβ, hφσ]

end A6Trans

end CFSG.Quasithin.H13
