module

public import CFSG.Quasithin.Background.C124BlkAlt
public import CFSG.Quasithin.Background.C124Dict
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.MS93.S32Nat

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {G : Type} [Group G] {A U : Subgroup G} (hU : IsElemAbelian 2 U)
  (hA : A ≤ Subgroup.normalizer (U : Set G))

@[expose] noncomputable def toAutI : ↥A →* ↥(autI hU A) :=
  (convHom hU A hA).codRestrict _ fun a => by
    rw [← range_convHom hU A hA]
    exact ⟨a, rfl⟩

theorem toAutI_surjective : Function.Surjective (toAutI hU hA) := by
  rintro ⟨x, hx⟩
  rw [← range_convHom hU A hA] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, rfl⟩

theorem toAutI_apply_val (a : ↥A) (u : IntMod U hU) :
    (((toAutI hU hA a : ↥(autI hU A)) : MulAut (IntMod U hU)) u).val = a * u.val * (a : G)⁻¹ :=
  convI_apply_val hU ⟨a, hA a.2⟩ u

@[expose] noncomputable def toTop : ↥U →* ↥(⊤ : Subgroup (IntMod U hU)) where
  toFun u := ⟨IntMod.mk hU u, Subgroup.mem_top _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toTop_bijective : Function.Bijective (toTop hU) :=
  ⟨fun _ _ h => congrArg (fun x : ↥(⊤ : Subgroup (IntMod U hU)) => (x : IntMod U hU)) h,
    fun x => ⟨(x : IntMod U hU), rfl⟩⟩

theorem toTop_val (u : ↥U) : ((toTop hU u : ↥(⊤ : Subgroup (IntMod U hU))) : IntMod U hU).val =
    (u : G) := rfl

theorem toAutI_toTop {a : ↥A} {u v : ↥U} (huv : (v : G) = a * u * a⁻¹) :
    ((toAutI hU hA a : ↥(autI hU A)) : MulAut (IntMod U hU)) (toTop hU u : IntMod U hU) =
      (toTop hU v : IntMod U hU) := by
  apply IntMod.val_injective
  rw [toAutI_apply_val, toTop_val, toTop_val, huv]
  simp

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}

include hA in
theorem isSumNat_one_of_realizesVia [Finite G] {Z' : Subgroup (IntMod U hU)}
    {π : ↥Γ →* ↥(autI hU A)} (hπ : (FFModel.nat Γ).RealizesVia (autI hU A) ⊤ Z' π) :
    ∃ α : ↥A →* ↥Γ, Function.Surjective α ∧
      IsSumOfNaturalModulesVia A U (C124.toG hU Z') α false 1 := by
  set e := FFC.equivOfRealizes (FFModel.nat_faithful Γ) hπ
  set α : ↥A →* ↥Γ := e.symm.toMonoidHom.comp (toAutI hU hA)
  have hπα : ∀ a : ↥A, π (α a) = toAutI hU hA a := fun a => e.apply_symm_apply _
  obtain ⟨β₀, hβs, hβk, hβe⟩ := natReal_coord hπ
  let fin1 : Multiplicative (ι → F) ≃* Multiplicative (Fin 1 → ι → F) :=
    (AddEquiv.funUnique (Fin 1) (ι → F)).symm.toMultiplicative
  refine ⟨α, e.symm.surjective.comp (toAutI_surjective hU hA), hA, C124.toG_le hU Z',
    fin1.toMonoidHom.comp (β₀.comp (toTop hU)), ?_, ?_, ?_⟩
  · exact fin1.surjective.comp (hβs.comp (toTop_bijective hU).2)
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
    rw [hβk, ← toTop_val hU u, C124.mem_toG_iff_of_mem hU]
  · intro a u v huv i
    have hu : ((π (α a) : ↥(autI hU A)) : MulAut (IntMod U hU)) (toTop hU u : IntMod U hU) ∈
        (⊤ : Subgroup (IntMod U hU)) := Subgroup.mem_top _
    have h1 := hβe (α a) (toTop hU u) hu
    have h2 : (⟨((π (α a) : ↥(autI hU A)) : MulAut (IntMod U hU)) (toTop hU u : IntMod U hU),
        hu⟩ : ↥(⊤ : Subgroup (IntMod U hU))) = toTop hU v := by
      apply Subtype.ext
      rw [hπα]
      exact toAutI_toTop hU hA huv
    rw [h2] at h1
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h1]
    simp [fin1, moduleAct]

@[expose] noncomputable def prodEquivOfCompl {V : Type*} [CommGroup V] (I₀ I₁ : Subgroup V)
    (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤) : ↥I₀ × ↥I₁ ≃* V :=
  MulEquiv.ofBijective (I₀.subtype.coprod I₁.subtype) ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      rintro ⟨a, b⟩ hab
      rw [MonoidHom.mem_ker, MonoidHom.coprod_apply] at hab
      have hab' : (a : V) = (b : V)⁻¹ := eq_inv_of_mul_eq_one_left hab
      have ha : (a : V) ∈ I₀ ⊓ I₁ := ⟨a.2, hab' ▸ I₁.inv_mem b.2⟩
      rw [hinf, Subgroup.mem_bot] at ha
      have hb : (b : V) = 1 := by rw [ha, eq_comm, inv_eq_one] at hab'; exact hab'
      rw [Subgroup.mem_bot]
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb),
    fun v => by
      have hv : v ∈ I₀ ⊔ I₁ := by rw [hsup]; exact Subgroup.mem_top v
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩⟩

theorem prodEquivOfCompl_apply {V : Type*} [CommGroup V] {I₀ I₁ : Subgroup V}
    (hinf : I₀ ⊓ I₁ = ⊥) (hsup : I₀ ⊔ I₁ = ⊤) (x : ↥I₀ × ↥I₁) :
    prodEquivOfCompl I₀ I₁ hinf hsup x = (x.1 : V) * (x.2 : V) := rfl

include hA in
theorem isSumNat_two_of_compl [Finite G] {I₀ I₁ : Subgroup (IntMod U hU)} (hinf : I₀ ⊓ I₁ = ⊥)
    (hsup : I₀ ⊔ I₁ = ⊤) {π : ↥Γ →* ↥(autI hU A)}
    (h₀ : (FFModel.nat Γ).RealizesVia (autI hU A) I₀ ⊥ π)
    (h₁ : (FFModel.nat Γ).RealizesVia (autI hU A) I₁ ⊥ π) :
    ∃ α : ↥A →* ↥Γ, Function.Surjective α ∧ IsSumOfNaturalModulesVia A U ⊥ α false 2 := by
  set e := FFC.equivOfRealizes (FFModel.nat_faithful Γ) h₀
  set α : ↥A →* ↥Γ := e.symm.toMonoidHom.comp (toAutI hU hA)
  have hπα : ∀ a : ↥A, π (α a) = toAutI hU hA a := fun a => e.apply_symm_apply _
  obtain ⟨β₀, hβs₀, hβk₀, hβe₀⟩ := natReal_coord h₀
  obtain ⟨β₁, hβs₁, hβk₁, hβe₁⟩ := natReal_coord h₁
  set d := prodEquivOfCompl I₀ I₁ hinf hsup
  let B : ↥I₀ × ↥I₁ →* Multiplicative (Fin 2 → ι → F) :=
    { toFun := fun x => Multiplicative.ofAdd
        ![Multiplicative.toAdd (β₀ x.1), Multiplicative.toAdd (β₁ x.2)]
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> simp
      map_mul' := fun x y => by
        apply Multiplicative.toAdd.injective
        funext i
        fin_cases i <;> simp }
  let j : ↥U →* IntMod U hU := (⊤ : Subgroup (IntMod U hU)).subtype.comp (toTop hU)
  refine ⟨α, e.symm.surjective.comp (toAutI_surjective hU hA), hA, bot_le,
    B.comp (d.symm.toMonoidHom.comp j), ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x₀, hx₀⟩ := hβs₀ (Multiplicative.ofAdd (Multiplicative.toAdd y 0))
    obtain ⟨x₁, hx₁⟩ := hβs₁ (Multiplicative.ofAdd (Multiplicative.toAdd y 1))
    obtain ⟨u, hu⟩ := (toTop_bijective hU).2 ⟨d (x₀, x₁), Subgroup.mem_top _⟩
    refine ⟨u, ?_⟩
    have hju : j u = d (x₀, x₁) := congrArg Subtype.val hu
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hju,
      MulEquiv.symm_apply_apply]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · simp [B, hx₀]
    · simp [B, hx₁]
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    constructor
    · intro hu
      set x := d.symm (j u) with hx
      have h0 : β₀ x.1 = 1 := by
        have := congrArg (fun m : Multiplicative (Fin 2 → ι → F) => Multiplicative.toAdd m 0) hu
        apply Multiplicative.toAdd.injective
        simpa [B, ← hx] using this
      have h1 : β₁ x.2 = 1 := by
        have := congrArg (fun m : Multiplicative (Fin 2 → ι → F) => Multiplicative.toAdd m 1) hu
        apply Multiplicative.toAdd.injective
        simpa [B, ← hx] using this
      rw [hβk₀, Subgroup.mem_bot] at h0
      rw [hβk₁, Subgroup.mem_bot] at h1
      have hju : j u = 1 := by
        rw [← d.apply_symm_apply (j u), ← hx, prodEquivOfCompl_apply, h0, h1, one_mul]
      have := congrArg IntMod.val hju
      exact this
    · intro hu
      have hu' : u = 1 := Subtype.ext hu
      rw [hu', map_one]
  · intro a u v huv i
    set g := ((π (α a) : ↥(autI hU A)) : MulAut (IntMod U hU)) with hgdef
    have hjv : j v = g (j u) := by
      rw [hgdef, hπα]
      exact (toAutI_toTop hU hA huv).symm
    set x := d.symm (j u) with hx
    have hg₀ : g (x.1 : IntMod U hU) ∈ I₀ := h₀.2.2.2.1 (π (α a)) _ x.1.2
    have hg₁ : g (x.2 : IntMod U hU) ∈ I₁ := h₁.2.2.2.1 (π (α a)) _ x.2.2
    have hdv : d.symm (j v) = (⟨g x.1, hg₀⟩, ⟨g x.2, hg₁⟩) := by
      apply d.injective
      rw [MulEquiv.apply_symm_apply, prodEquivOfCompl_apply, hjv, ← map_mul,
        ← prodEquivOfCompl_apply hinf hsup x, hx, MulEquiv.apply_symm_apply]
    have e₀ := hβe₀ (α a) x.1 hg₀
    have e₁ := hβe₁ (α a) x.2 hg₁
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hdv, ← hx]
    fin_cases i
    · simp only [B, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
      rw [e₀]
      simp [moduleAct]
    · simp only [B, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
      rw [e₁]
      simp [moduleAct]

include hA in
theorem isAltNaturalSection_of_realizesVia [Finite G] {Z' : Subgroup (IntMod U hU)} {n : ℕ}
    (hn : 5 ≤ n) {π : ↥(alternatingGroup (Fin n)) →* ↥(autI hU A)}
    (hπ : (FFModel.altDn n).RealizesVia (autI hU A) ⊤ Z' π) :
    ∃ N : Subgroup ↥A, IsAltNaturalSection A U (C124.toG hU Z') N n := by
  have hn0 : 0 < n := by omega
  set eπ := FFC.equivOfRealizes (FFC.altDn_faithful hn) hπ
  set α : ↥A →* alternatingGroup (Fin n) := eπ.symm.toMonoidHom.comp (toAutI hU hA)
  have hπα : ∀ a : ↥A, π (α a) = toAutI hU hA a := fun a => eπ.apply_symm_apply _
  obtain ⟨-, -, -, -, -, -, -, β₁, hβs, hβk, hβe⟩ := id hπ
  let β₁' : ↥(⊤ : Subgroup (IntMod U hU)) →* (↥(G6.coreMod n) ⧸ C124.altKer n) := β₁
  set β : ↥U →* Multiplicative (AltHeart n) :=
    (C124.altQuotEquiv n hn0).toMonoidHom.comp (β₁'.comp (toTop hU))
  refine ⟨α.ker, hA, α, eπ.symm.surjective.comp (toAutI_surjective hU hA), rfl, β, ?_, ?_, ?_⟩
  · exact (C124.altQuotEquiv n hn0).surjective.comp (hβs.comp (toTop_bijective hU).2)
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have e1 : β u = 1 ↔ β₁ (toTop hU u) = 1 := by
      show (C124.altQuotEquiv n hn0) (β₁' (toTop hU u)) = 1 ↔ _
      exact (C124.altQuotEquiv n hn0).map_eq_one_iff
    rw [e1, hβk, ← toTop_val hU u, C124.mem_toG_iff_of_mem hU]
  · intro a u v huv x hx
    set γ := α a
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₁ (toTop hU u))
    have hact : (FFModel.altDn n).act γ (m : (FFModel.altDn n).Amb) ∈ (FFModel.altDn n).sec :=
      G6.permAct_mem_coreMod _ m.2
    have hu : ((π γ : ↥(autI hU A)) : MulAut (IntMod U hU)) (toTop hU u : IntMod U hU) ∈
        (⊤ : Subgroup (IntMod U hU)) := Subgroup.mem_top _
    have h1 := hβe γ (toTop hU u) m hu hact hm.symm
    have h2 : (⟨((π γ : ↥(autI hU A)) : MulAut (IntMod U hU)) (toTop hU u : IntMod U hU),
        hu⟩ : ↥(⊤ : Subgroup (IntMod U hU))) = toTop hU v := by
      apply Subtype.ext
      rw [hπα]
      exact toAutI_toTop hU hA huv
    have h1' : β₁ (toTop hU v) = QuotientGroup.mk ⟨_, hact⟩ := by rw [← h2]; exact h1
    have hβu : β u = C124.altHeartHom n m := by
      show C124.altQuotEquiv n hn0 (β₁ (toTop hU u)) = _
      rw [← hm]
      rfl
    have h3 : Multiplicative.toAdd (β v) = (QuotientAddGroup.mk
        (permWeight n (γ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (C124.coreEvenEquiv n m))) :
          AltHeart n) := by
      show Multiplicative.toAdd (C124.altQuotEquiv n hn0 (β₁ (toTop hU v))) = _
      rw [h1']
      rfl
    rw [h3]
    have h4 : (QuotientAddGroup.mk x : AltHeart n) =
        QuotientAddGroup.mk (Multiplicative.toAdd (C124.coreEvenEquiv n m)) := by
      rw [hx, hβu]
      rfl
    rw [QuotientAddGroup.eq] at h4 ⊢
    exact C124.permWeight_sub_mem _ h4

end CFSG.Quasithin.MS93.S32
