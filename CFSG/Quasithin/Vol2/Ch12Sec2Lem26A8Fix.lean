module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem26A8B51
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem26A8Sh
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem26A8S0
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique Equiv
open scoped IsMulCommutative

namespace Lem26A8

section Coord

variable {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)}

theorem exists_coord {π : ↥(alternatingGroup (Fin 8)) →* ↥K}
    {β : ↥(⊤ : Subgroup W) →* ↥(altCoreModel 8).sec ⧸
      (altCoreModel 8).ker.subgroupOf (altCoreModel 8).sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy (altCoreModel 8) K ⊤ ⊥ π β) :
    ∃ κ : W →* G6.PermMod 8, Function.Injective κ ∧ (∀ a, κ a ∈ G6.coreMod 8) ∧
      (∀ m ∈ G6.coreMod 8, ∃ a, κ a = m) ∧
      ∀ γ a, κ (((π γ : ↥K) : MulAut W) a) = G6.permAct 8 (γ : Perm (Fin 8)) (κ a) := by
  classical
  have hmk : ∀ m m' : ↥(altCoreModel 8).sec,
      (QuotientGroup.mk m : ↥(altCoreModel 8).sec ⧸
        (altCoreModel 8).ker.subgroupOf (altCoreModel 8).sec) = QuotientGroup.mk m' → m = m' := by
    intro m m' h
    have h1 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (m⁻¹ * m').1 = 1 := (Subgroup.mem_bot).mp h1
    have h3 : m⁻¹ * m' = 1 := Subtype.ext h2
    exact (inv_mul_eq_one.mp h3)
  choose f hf using fun a : W => QuotientGroup.mk_surjective (Orbit.coordOf β a)
  have hfmul : ∀ a b, f (a * b) = f a * f b := fun a b =>
    hmk _ _ (by rw [QuotientGroup.mk_mul, hf, hf, hf, Orbit.coordOf_mul])
  have hf1 : f 1 = 1 := hmk _ _ (by rw [hf, Orbit.coordOf_one, QuotientGroup.mk_one])
  refine ⟨{ toFun := fun a => show G6.PermMod 8 from (f a).1
            map_one' := by rw [hf1]; rfl
            map_mul' := fun a b => by rw [hfmul]; rfl }, ?_, ?_, ?_, ?_⟩
  · intro a b h
    apply Orbit.coordOf_injective hR
    have h' : f a = f b := Subtype.ext h
    rw [← hf a, ← hf b, h']
  · intro a
    exact (f a).2
  · intro m hm
    obtain ⟨a, ha⟩ := Orbit.coordOf_surjective hR (QuotientGroup.mk ⟨m, hm⟩)
    exact ⟨a, congrArg Subtype.val (hmk _ _ ((hf a).trans ha))⟩
  · intro γ a
    have h1 := Orbit.coordOf_act hR γ a (f a) (hf a).symm
    rw [← hf] at h1
    exact congrArg Subtype.val (hmk _ _ h1)

end Coord

theorem eq_one_or_allOnes_of_fixed {w : G6.PermMod 8}
    (hw : ∀ γ : alternatingGroup (Fin 8), G6.permAct 8 (γ : Perm (Fin 8)) w = w) :
    w = 1 ∨ w = G6.allOnes 8 := by
  have := alternatingGroup.isPretransitive_of_three_le_card (Fin 8) (by simp)
  have hc : ∀ i, Multiplicative.toAdd w i = Multiplicative.toAdd w 0 := by
    intro i
    obtain ⟨γ, hγ⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) (0 : Fin 8) i
    have h1 := congrArg (fun y : G6.PermMod 8 => Multiplicative.toAdd y i) (hw γ)
    simp only [G6.permAct_apply] at h1
    have e : (γ : Perm (Fin 8))⁻¹ i = 0 := by
      rw [← hγ]
      show (γ : Perm (Fin 8))⁻¹ ((γ : Perm (Fin 8)) 0) = 0
      rw [Perm.inv_def, Equiv.symm_apply_apply]
    rw [← h1, e]
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h01 (Multiplicative.toAdd w 0) with h | h
  · left
    apply Multiplicative.toAdd.injective
    funext i
    rw [hc i, h]
    rfl
  · right
    apply Multiplicative.toAdd.injective
    funext i
    rw [hc i, h]
    rfl

theorem mem_autOn_iff' {G : Type} [Group G] {H V : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (V : Set G)) {φ : MulAut ↥V} :
    φ ∈ autOn H V ↔ ∃ h ∈ H, ∀ a : ↥V, ((φ a : ↥V) : G) = h * a * h⁻¹ := by
  rw [A4.mem_autOn_iff hH]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, h.2, fun a => A4.actionOn_apply_coe hH h a⟩
  · rintro ⟨h, hh, he⟩
    refine ⟨⟨h, hh⟩, MulEquiv.ext fun a => Subtype.ext ?_⟩
    rw [A4.actionOn_apply_coe, he]

namespace Cfg

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {z v g : G}
  (c : Cfg T L V z v g)
include c

theorem exists_realizesBy [IsMulCommutative ↥V] :
    ∃ (π : ↥(alternatingGroup (Fin 8)) →* ↥(autOn L V))
      (β : ↥(⊤ : Subgroup ↥V) →* ↥(altCoreModel 8).sec ⧸
        (altCoreModel 8).ker.subgroupOf (altCoreModel 8).sec),
      Function.Injective π ∧
        CFSG.Quasithin.H.Mathieu.RealizesBy (altCoreModel 8) (autOn L V) ⊤ ⊥ π β := by
  obtain ⟨π, β, hR⟩ := (CFSG.Quasithin.H.Mathieu.realizes_iff _ _ _ _).mp c.real
  refine ⟨π, β, ?_, hR⟩
  have hLV := c.LV
  have : IsSimpleGroup (altCoreModel 8).Gam :=
    alternatingGroup.isSimpleGroup (α := Fin 8)
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hne : ∃ a : ↥(autOn L V), a ≠ 1 := by
    by_contra hall
    push Not at hall
    apply not_le_centralizer_of_hyp1223 c.hyp
    intro l hl
    exact (mem_ker_autOnSurj hLV ⟨l, hl⟩).mp (hall _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff π).mp h
  · exfalso
    obtain ⟨a, ha⟩ := hne
    obtain ⟨x, rfl⟩ := hR.1 a
    exact ha ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top x))

theorem exists_decomp [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2)
    (h3228 : Stmt3_2_2_eight)
    (hcomm : ⁅conjClosure (quasithinOmegaOneCenter (T ⊓ Subgroup.centralizer ({v} : Set G))) L,
      L⁆ = V)
    {x : G} (hxT : x ∈ T ⊓ Subgroup.centralizer ({v} : Set G))
    (hxC : x ∈ Subgroup.centralizer ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) :
      Set G))
    (hx2 : x ^ 2 = 1) :
    ∃ a ∈ V, a ∈ Subgroup.centralizer
        ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) ∧
      ∃ b ∈ T ⊓ Subgroup.centralizer ({v} : Set G), b ∈ Subgroup.centralizer
        ((T ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) : Set G) ∧
        b ∈ Subgroup.centralizer (L : Set G) ∧ x = a * b := by
  classical
  obtain ⟨hVvQ, hVvC, -, hN, hVV⟩ := c.vv_facts h1222 h3228
  set Tv := T ⊓ Subgroup.centralizer ({v} : Set G) with hTv
  set Vv := conjClosure (quasithinOmegaOneCenter Tv) L with hVvdef
  obtain ⟨hVT, hred, hV2⟩ := c.facts h1222
  have hLV := c.LV
  have hab : ∀ y ∈ Vv, ∀ w ∈ Vv, y * w = w * y := fun y hy w hw =>
    (Subgroup.mem_centralizer_iff.mp (hVvC hy) w (hVvQ hw)).symm
  have hxVv : x ∈ Vv := le_conjClosure _ L (mem_omega.mpr ⟨hxT, hxC, hx2⟩)
  have hVTv : V ≤ Tv := fun a ha => ⟨hVT ha, Subgroup.mem_centralizer_singleton_iff.mpr
    (hab a (hVV ha) v (hVV c.vV))⟩
  have hind : ∀ l ∈ L, ∀ l' ∈ L, (∀ a ∈ V, l * a * l⁻¹ = l' * a * l'⁻¹) →
      ∀ y ∈ Vv, l * y * l⁻¹ = l' * y * l'⁻¹ := by
    intro l hl l' hl' h y hy
    have h1 : l'⁻¹ * l ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      calc a * (l'⁻¹ * l) = l'⁻¹ * (l' * a * l'⁻¹) * l := by group
        _ = l'⁻¹ * (l * a * l⁻¹) * l := by rw [h a ha]
        _ = l'⁻¹ * l * a := by group
    have h2 := Subgroup.mem_centralizer_iff.mp (c.inf_centralizer_le_vv h1222 h3228
      ⟨Subgroup.mem_sup_left (L.mul_mem (L.inv_mem hl') hl), h1⟩) y hy
    calc l * y * l⁻¹ = l' * ((l'⁻¹ * l) * y) * l⁻¹ := by group
      _ = l' * (y * (l'⁻¹ * l)) * l⁻¹ := by rw [h2]
      _ = l' * y * l'⁻¹ := by group
  obtain ⟨π, β, hπi, hR⟩ := c.exists_realizesBy
  have hπs : Function.Surjective π := hR.1
  obtain ⟨κ, hκi, hκE, hκs, hκact⟩ := exists_coord hR
  choose lf hlf using fun γ => (A4.mem_autOn_iff hLV).mp (π γ).2
  have hact : ∀ γ (a : ↥V), ((((π γ : ↥(autOn L V)) : MulAut ↥V) a : ↥V) : G) =
      (lf γ : G) * a * (lf γ : G)⁻¹ := by
    intro γ a
    rw [← hlf γ, A4.actionOn_apply_coe]
  have hsurjL : ∀ l ∈ L, ∃ γ, ∀ a ∈ V, (lf γ : G) * a * (lf γ : G)⁻¹ = l * a * l⁻¹ := by
    intro l hl
    obtain ⟨γ, hγ⟩ := hπs ⟨A4.actionOn V L hLV ⟨l, hl⟩, (A4.mem_autOn_iff hLV).mpr ⟨_, rfl⟩⟩
    refine ⟨γ, fun a ha => ?_⟩
    rw [← hact γ ⟨a, ha⟩, hγ, A4.actionOn_apply_coe]
  have hfV : ∀ γ, (lf γ : G) * x * (lf γ : G)⁻¹ * x⁻¹ ∈ V := by
    intro γ
    rw [← hcomm, Subgroup.commutator_comm]
    have := Subgroup.commutator_mem_commutator (lf γ).2 hxVv
    rwa [commutatorElement_def] at this
  let f : alternatingGroup (Fin 8) → ↥V := fun γ => ⟨_, hfV γ⟩
  have hfmul : ∀ γ γ', f (γ * γ') =
      ((π γ : ↥(autOn L V)) : MulAut ↥V) (f γ') * f γ := by
    intro γ γ'
    apply Subtype.ext
    have h1 : ∀ a ∈ V, (lf (γ * γ') : G) * a * (lf (γ * γ') : G)⁻¹ =
        ((lf γ : G) * lf γ') * a * ((lf γ : G) * lf γ')⁻¹ := by
      intro a ha
      have e1 := hact (γ * γ') ⟨a, ha⟩
      rw [map_mul, Subgroup.coe_mul, MulAut.mul_apply, hact γ, hact γ'] at e1
      rw [← e1]
      group
    have h2 := hind _ (lf (γ * γ')).2 _ (L.mul_mem (lf γ).2 (lf γ').2) h1 x hxVv
    show (lf (γ * γ') : G) * x * (lf (γ * γ') : G)⁻¹ * x⁻¹ =
      ((((π γ : ↥(autOn L V)) : MulAut ↥V) (f γ') : ↥V) : G) * ((f γ : ↥V) : G)
    rw [hact γ, h2]
    show _ = (lf γ : G) * ((lf γ' : G) * x * (lf γ' : G)⁻¹ * x⁻¹) * (lf γ : G)⁻¹ *
      ((lf γ : G) * x * (lf γ : G)⁻¹ * x⁻¹)
    group
  let cc : alternatingGroup (Fin 8) → Fin 8 → ZMod 2 := fun γ y => Multiplicative.toAdd (κ (f γ)) y
  have hcc : ∀ γ γ' y, cc (γ * γ') y = cc γ y + cc γ' (γ⁻¹ • y) := by
    intro γ γ' y
    show Multiplicative.toAdd (κ (f (γ * γ'))) y = Multiplicative.toAdd (κ (f γ)) y +
      Multiplicative.toAdd (κ (f γ')) (γ⁻¹ • y)
    rw [hfmul, map_mul, hκact, toAdd_mul, Pi.add_apply, G6.permAct_apply, add_comm]
    rfl
  obtain ⟨e, he⟩ := exists_coboundary_alternatingGroup (α := Fin 8) (by simp) cc hcc
  set ê : G6.PermMod 8 := Multiplicative.ofAdd e with hê
  have hκf : ∀ γ, κ (f γ) = G6.permAct 8 (γ : Perm (Fin 8)) ê * ê := by
    intro γ
    apply Multiplicative.toAdd.injective
    funext y
    rw [toAdd_mul, Pi.add_apply, G6.permAct_apply]
    exact he γ y
  have hsq : ∀ w : G6.PermMod 8, w * w = 1 := fun w => by
    apply Multiplicative.toAdd.injective
    funext i
    rw [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
    generalize Multiplicative.toAdd w i = a
    revert a
    decide
  set v' : ↥V := ⟨v, c.vV⟩ with hv'
  set z' : ↥V := ⟨z, c.zV⟩ with hz'
  set u := κ v' with hu
  have hκz : κ z' = G6.allOnes 8 := by
    have hfix : ∀ γ : alternatingGroup (Fin 8), G6.permAct 8 (γ : Perm (Fin 8)) (κ z') = κ z' := by
      intro γ
      rw [← hκact]
      congr 1
      apply Subtype.ext
      rw [hact]
      have := Subgroup.mem_centralizer_iff.mp c.zVL.2 _ (lf γ).2
      show (lf γ : G) * z * (lf γ : G)⁻¹ = z
      rw [this, mul_inv_cancel_right]
    rcases eq_one_or_allOnes_of_fixed hfix with h | h
    · exfalso
      apply c.z1
      have := hκi (h.trans (map_one κ).symm)
      exact congrArg Subtype.val this
    · exact h
  have hwt : Orbit.wtP u = 2 ∨ Orbit.wtP u = 6 := by
    have hev := (Orbit.mem_coreMod_iff u).mp (hκE v')
    have hle := Orbit.wtP_le u
    have h0 : Orbit.wtP u ≠ 0 := by
      intro h
      apply c.v1
      have := hκi ((Orbit.wtP_eq_zero.mp h).trans (map_one κ).symm)
      exact congrArg Subtype.val this
    have h8 : Orbit.wtP u ≠ 8 := by
      intro h
      apply c.vz
      have h1 := (Orbit.wtP_eq_self_iff.mp h).trans hκz.symm
      have := congrArg Subtype.val (hκi h1)
      rw [show ((v' : ↥V) : G) = v from rfl] at this
      rw [this]
      exact Subgroup.mem_zpowers z
    have h4 : Orbit.wtP u ≠ 4 := by
      intro h
      have h1 : Orbit.wtP (u * G6.allOnes 8) = Orbit.wtP u := by
        rw [Orbit.wtP_mul_allOnes, h]
      obtain ⟨σ, hσ, hσe⟩ := Orbit.exists_alt_permAct_eq (by norm_num : 3 ≤ 8) h1.symm
      have h2 : κ (((π ⟨σ, hσ⟩ : ↥(autOn L V)) : MulAut ↥V) v') = κ (v' * z') := by
        rw [hκact, map_mul, hκz]
        exact hσe
      have h3 := congrArg Subtype.val (hκi h2)
      rw [hact] at h3
      apply c.not_conj _ (Subgroup.le_normalizer (lf ⟨σ, hσ⟩).2)
      exact h3
    obtain ⟨k, hk⟩ := hev
    omega
  set A₂ := Tv ⊓ L with hA₂
  set A₁ := L ⊓ Subgroup.centralizer ({v} : Set G) with hA₁
  have hA₂N : A₂ ≤ Subgroup.normalizer (V : Set G) := fun t ht => c.TV ht.1.1
  have hA₁N : A₁ ≤ Subgroup.normalizer (V : Set G) := fun l hl => hLV hl.1
  have hcard : ∀ K' : Subgroup (MulAut ↥V), K' ≤ autOn L V →
      Nat.card ((K'.subgroupOf (autOn L V)).comap π) = Nat.card K' := by
    intro K' hK'
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK').toEquiv]
    refine Nat.card_congr (Equiv.ofBijective (fun γ => ⟨π γ, γ.2⟩) ⟨fun a b h =>
      Subtype.ext (hπi (congrArg Subtype.val h)), fun y => ?_⟩)
    obtain ⟨γ, hγ⟩ := hπs y
    exact ⟨⟨γ, by rw [Subgroup.mem_comap, hγ]; exact y.2⟩, Subtype.ext hγ⟩
  set S : Subgroup (alternatingGroup (Fin 8)) := ((autOn A₂ V).subgroupOf (autOn L V)).comap π
    with hSdef
  have hmemS : ∀ γ, γ ∈ S ↔ ∃ t ∈ A₂, ∀ a ∈ V, (lf γ : G) * a * (lf γ : G)⁻¹ = t * a * t⁻¹ := by
    intro γ
    rw [hSdef, Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_autOn_iff' hA₂N]
    constructor
    · rintro ⟨t, ht, he⟩
      exact ⟨t, ht, fun a ha => by rw [← hact γ ⟨a, ha⟩, he]⟩
    · rintro ⟨t, ht, he⟩
      exact ⟨t, ht, fun a => by rw [hact γ, he a a.2]⟩
  have hcv : ∀ t ∈ Subgroup.centralizer ({v} : Set G), t * v * t⁻¹ = v := fun t ht => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp ht, mul_inv_cancel_right]
  have hfixv : ∀ γ : alternatingGroup (Fin 8),
      G6.permAct 8 (γ : Perm (Fin 8)) u = u ↔ (lf γ : G) * v * (lf γ : G)⁻¹ = v := by
    intro γ
    rw [hu, ← hκact]
    constructor
    · intro h
      have := congrArg Subtype.val (hκi h)
      rwa [hact] at this
    · intro h
      congr 1
      apply Subtype.ext
      rw [hact]
      exact h
  have hSu : S ≤ stabU u := by
    intro γ hγ
    obtain ⟨t, ht, he⟩ := (hmemS γ).mp hγ
    rw [mem_stabU, hfixv, he v c.vV]
    exact hcv t ht.1.2
  have hstab : stabU u = ((autOn A₁ V).subgroupOf (autOn L V)).comap π := by
    ext γ
    rw [mem_stabU, hfixv, Subgroup.mem_comap, Subgroup.mem_subgroupOf, mem_autOn_iff' hA₁N]
    constructor
    · intro h
      refine ⟨lf γ, ⟨(lf γ).2, ?_⟩, fun a => hact γ a⟩
      show (lf γ : G) ∈ Subgroup.centralizer ({v} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (lf γ : G) * v = (lf γ : G) * v * (lf γ : G)⁻¹ * lf γ := by group
        _ = v * lf γ := by rw [h]
    · rintro ⟨l, hl, he⟩
      rw [← hact γ v', he v']
      exact hcv l hl.2
  have hVe : IsElemAbelian 2 V := ⟨c.comm, hV2⟩
  have hc1 := card_autI_mul_card_inf hVe hA₁N
  have hc2 := card_autI_mul_card_inf hVe hA₂N
  change Nat.card ↥(autOn A₁ V) * _ = _ at hc1
  change Nat.card ↥(autOn A₂ V) * _ = _ at hc2
  have hk : A₁ ⊓ Subgroup.centralizer (V : Set G) = A₂ ⊓ Subgroup.centralizer (V : Set G) := by
    apply le_antisymm
    · rintro y ⟨⟨hyL, hyv⟩, hyC⟩
      have hyT : y ∈ T := pCoreOf_le_of_le_normalizer c.hyp.sylow c.hyp.normalizes
        (c.inf_centralizer_le h1222 ⟨hyL, hyC⟩)
      exact ⟨⟨⟨hyT, hyv⟩, hyL⟩, hyC⟩
    · rintro y ⟨⟨⟨-, hyv⟩, hyL⟩, hyC⟩
      exact ⟨⟨hyL, hyv⟩, hyC⟩
  have hsylA : IsSylowTwoOf (Tv ⊓ A₁) A₁ := by
    refine A4.isSylowTwoOf_inf_normal c.syl inf_le_right ?_
    refine le_trans (le_inf (c.noEsc v c.vV c.v1) Subgroup.le_normalizer)
      Subgroup.inf_normalizer_le_normalizer_inf
  have hA₂eq : Tv ⊓ A₁ = A₂ := by
    apply le_antisymm
    · rintro y ⟨hyT, hyL, -⟩
      exact ⟨hyT, hyL⟩
    · rintro y ⟨hyT, hyL⟩
      exact ⟨hyT, hyL, hyT.2⟩
  rw [hA₂eq] at hsylA
  have hidx := Subgroup.card_mul_index (A₂.subgroupOf A₁)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsylA.1).toEquiv] at hidx
  have h720 : Nat.card ↥(autOn A₁ V) = 720 := by
    rw [← hcard _ (InternalSec.autOn_le_autOn_of_le inf_le_left), ← hstab]
    exact card_stabU hwt
  have hA₂2 : IsPGroup 2 ↥A₂ := c.syl.2.1.to_le inf_le_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m₂, hm₂⟩ := IsPGroup.iff_card.mp hA₂2
  have hdvd : Nat.card ↥(autOn A₂ V) ∣ 2 ^ m₂ := hm₂ ▸ Dvd.intro _ hc2
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hpos : 0 < Nat.card ↥(A₂ ⊓ Subgroup.centralizer (V : Set G)) := Nat.card_pos
  have hS16 : Nat.card S = 16 := by
    rw [hSdef, hcard _ (InternalSec.autOn_le_autOn_of_le inf_le_right), hm]
    have e1 : 720 * Nat.card ↥(A₂ ⊓ Subgroup.centralizer (V : Set G)) =
        2 ^ m * Nat.card ↥(A₂ ⊓ Subgroup.centralizer (V : Set G)) * (A₂.subgroupOf A₁).index := by
      rw [h720, hk] at hc1
      rw [hc1, ← hidx, ← hc2, hm]
    have e2 : 720 = 2 ^ m * (A₂.subgroupOf A₁).index := by
      have := e1
      rw [mul_comm (2 ^ m), mul_assoc] at this
      exact Nat.eq_of_mul_eq_mul_right hpos (by linarith)
    have hodd := hsylA.2.2
    have hm10 : m < 10 := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ 10 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hlt
      have hi : 0 < (A₂.subgroupOf A₁).index := Nat.pos_of_ne_zero (fun h => by
        rw [h, mul_zero] at e2; norm_num at e2)
      nlinarith
    interval_cases m <;> omega
  obtain ⟨hM1, q, hqS, hqwt, hqu, hcl, hwq⟩ := fixed_of_card hwt hSu hS16
  have hSx : ∀ γ ∈ S, (lf γ : G) * x * (lf γ : G)⁻¹ = x := by
    intro γ hγ
    obtain ⟨t, ht, he⟩ := (hmemS γ).mp hγ
    rw [hind _ (lf γ).2 _ ht.2 he x hxVv]
    rw [Subgroup.mem_centralizer_iff.mp hxC t ht.1, mul_inv_cancel_right]
  have hêS : ∀ γ ∈ S, G6.permAct 8 (γ : Perm (Fin 8)) ê = ê := by
    intro γ hγ
    have h1 : f γ = 1 := by
      apply Subtype.ext
      show (lf γ : G) * x * (lf γ : G)⁻¹ * x⁻¹ = 1
      rw [hSx γ hγ, mul_inv_cancel]
    have h2 := hκf γ
    rw [h1, map_one] at h2
    have h3 := congrArg (· * ê) h2.symm
    simp only [one_mul] at h3
    rwa [mul_assoc, hsq, mul_one] at h3
  have hev : ê ∈ G6.coreMod 8 := (Orbit.mem_coreMod_iff ê).mpr (hM1 ê fun γ hγ => hêS γ hγ)
  obtain ⟨a₀, ha₀⟩ := hκs ê hev
  set a : G := (a₀ : G) with ha
  have haV : a ∈ V := a₀.2
  have hfa : ∀ γ, (lf γ : G) * x * (lf γ : G)⁻¹ * x⁻¹ = (lf γ : G) * a * (lf γ : G)⁻¹ * a := by
    intro γ
    have h1 : κ (f γ) = κ ((((π γ : ↥(autOn L V)) : MulAut ↥V) a₀) * a₀) := by
      rw [hκf, map_mul, hκact, ha₀]
    have h2 := congrArg Subtype.val (hκi h1)
    rw [Subgroup.coe_mul, hact] at h2
    exact h2
  have hsqV : ∀ y ∈ V, y * y = 1 := fun y hy => by rw [← pow_two]; exact hV2 y hy
  have hbL : x * a ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨γ, hγ⟩ := hsurjL l hl
    have hxa : x * a ∈ Vv := Vv.mul_mem hxVv (hVV haV)
    have h1 := hind _ (lf γ).2 _ hl hγ (x * a) hxa
    set p := (lf γ : G) * a * (lf γ : G)⁻¹ with hp
    have hpV : p ∈ V := (Subgroup.mem_normalizer_iff.mp (hLV (lf γ).2) a).mp haV
    have h2 : (lf γ : G) * (x * a) * (lf γ : G)⁻¹ = x * a := by
      calc (lf γ : G) * (x * a) * (lf γ : G)⁻¹ =
            ((lf γ : G) * x * (lf γ : G)⁻¹ * x⁻¹) * x * p := by rw [hp]; group
        _ = p * a * x * p := by rw [hfa γ]
        _ = p * p * (a * x) := by
          rw [mul_assoc p a x, mul_assoc, hab (a * x) (Vv.mul_mem (hVV haV) hxVv) p (hVV hpV),
            ← mul_assoc]
        _ = x * a := by rw [hsqV p hpV, one_mul, hab a (hVV haV) x hxVv]
    calc l * (x * a) = l * (x * a) * l⁻¹ * l := by group
      _ = x * a * l := by rw [← h1, h2]
  have hdec : x = a * (x * a) := by
    rw [← mul_assoc, hab a (hVV haV) x hxVv, mul_assoc, hsqV a haV, mul_one]
  have haA₂ : ∀ t ∈ A₂, t * a * t⁻¹ = a := by
    intro t ht
    have h1 : t * x * t⁻¹ = x := by
      rw [Subgroup.mem_centralizer_iff.mp hxC t ht.1, mul_inv_cancel_right]
    have h2 : t * (x * a) * t⁻¹ = x * a := by
      rw [Subgroup.mem_centralizer_iff.mp hbL t ht.2, mul_inv_cancel_right]
    calc t * a * t⁻¹ = (t * x * t⁻¹)⁻¹ * (t * (x * a) * t⁻¹) := by group
      _ = a := by rw [h1, h2]; group
  have hfixS : ∀ b : ↥V, (∀ t ∈ A₂, t * (b : G) * t⁻¹ = b) →
      ∀ γ ∈ S, G6.permAct 8 (γ : Perm (Fin 8)) (κ b) = κ b := by
    intro b hb γ hγ
    obtain ⟨t, ht, he⟩ := (hmemS γ).mp hγ
    rw [← hκact]
    congr 1
    apply Subtype.ext
    rw [hact, he b b.2, hb t ht]
  have hfixA : ∀ b : ↥V, (∀ γ ∈ S, G6.permAct 8 (γ : Perm (Fin 8)) (κ b) = κ b) →
      ∀ t ∈ A₂, t * (b : G) * t⁻¹ = b := by
    intro b hb t ht
    obtain ⟨γ, hγ⟩ := hsurjL t ht.2
    have hγS : γ ∈ S := (hmemS γ).mpr ⟨t, ht, hγ⟩
    have h1 := hb γ hγS
    rw [← hκact] at h1
    have h2 := congrArg Subtype.val (hκi h1)
    rw [hact, hγ b b.2] at h2
    exact h2
  have hqE : q ∈ G6.coreMod 8 := (Orbit.mem_coreMod_iff q).mpr (hM1 q hqS)
  obtain ⟨q', hq'⟩ := hκs q hqE
  have hq'A : ∀ t ∈ A₂, t * (q' : G) * t⁻¹ = q' := hfixA q' (by rw [hq']; exact hqS)
  obtain ⟨σ₀, hσ₀, hσ₀e⟩ := Orbit.exists_alt_permAct_eq (by norm_num : 3 ≤ 8) hqwt.symm
  have hq'L : (lf ⟨σ₀, hσ₀⟩ : G) * v * (lf ⟨σ₀, hσ₀⟩ : G)⁻¹ = q' := by
    have h1 : κ (((π ⟨σ₀, hσ₀⟩ : ↥(autOn L V)) : MulAut ↥V) v') = κ q' := by
      rw [hκact, hq']
      exact hσ₀e
    have h2 := congrArg Subtype.val (hκi h1)
    rw [hact] at h2
    exact h2
  have htq : ∀ t ∈ Tv, t * (q' : G) * t⁻¹ = q' := by
    intro t ht
    set l₀ : G := (lf ⟨σ₀, hσ₀⟩ : G) with hl₀
    have hl₀L : l₀ ∈ L := (lf ⟨σ₀, hσ₀⟩).2
    have htN : t ∈ Subgroup.normalizer (L : Set G) := c.hyp.normalizes ht.1
    have hl₁ : t * l₀ * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htN l₀).mp hl₀L
    have hyV : t * (q' : G) * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (c.TV ht.1) _).mp q'.2
    set y : ↥V := ⟨_, hyV⟩ with hy
    have hyl : (y : G) = (t * l₀ * t⁻¹) * v * (t * l₀ * t⁻¹)⁻¹ := by
      rw [hy]
      show t * (q' : G) * t⁻¹ = _
      rw [← hq'L]
      calc t * (l₀ * v * l₀⁻¹) * t⁻¹ = (t * l₀ * t⁻¹) * (t * v * t⁻¹) * (t * l₀ * t⁻¹)⁻¹ := by
            group
        _ = _ := by rw [hcv t ht.2]
    have hyA : ∀ t' ∈ A₂, t' * (y : G) * t'⁻¹ = y := by
      intro t' ht'
      have htt : t⁻¹ * t' * t ∈ A₂ := by
        refine ⟨Tv.mul_mem (Tv.mul_mem (Tv.inv_mem ht) ht'.1) ht, ?_⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) t').mp ht'.2
        simpa using this
      have h1 := hq'A _ htt
      show t' * (t * (q' : G) * t⁻¹) * t'⁻¹ = t * (q' : G) * t⁻¹
      calc t' * (t * (q' : G) * t⁻¹) * t'⁻¹ =
            t * ((t⁻¹ * t' * t) * (q' : G) * (t⁻¹ * t' * t)⁻¹) * t⁻¹ := by group
        _ = t * (q' : G) * t⁻¹ := by rw [h1]
    have hyS := hfixS y hyA
    obtain ⟨γ₁, hγ₁⟩ := hsurjL _ hl₁
    have hyw : κ y = G6.permAct 8 (γ₁ : Perm (Fin 8)) u := by
      rw [hu, ← hκact]
      congr 1
      apply Subtype.ext
      rw [hact, hγ₁ v c.vV, ← hyl]
    have hwy : Orbit.wtP (κ y) = Orbit.wtP u := by rw [hyw, Orbit.wtP_permAct]
    rcases hwq (κ y) hyS hwy with h | h
    · exfalso
      apply hqu
      have h1 := congrArg Subtype.val (hκi (h.trans hu))
      have h2 : (q' : G) = v := by
        have h3 : t * (q' : G) * t⁻¹ = v := h1
        calc (q' : G) = t⁻¹ * (t * (q' : G) * t⁻¹) * t := by group
          _ = t⁻¹ * v * t := by rw [h3]
          _ = v := by
            have := hcv t⁻¹ (Subgroup.inv_mem _ ht.2)
            rw [inv_inv] at this
            exact this
      rw [← hq', hu]
      congr 1
      exact Subtype.ext h2
    · exact congrArg Subtype.val (hκi (h.trans hq'.symm))
  have hmemcl : a₀ ∈ Subgroup.closure ({v', q', z'} : Set ↥V) := by
    have h1 := hcl ê (fun γ hγ => hêS γ hγ)
    rw [← ha₀, show ({u, q, G6.allOnes 8} : Set (G6.PermMod 8)) = κ '' {v', q', z'} by
      rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, ← hu, hq', hκz],
      ← MonoidHom.map_closure] at h1
    exact (Subgroup.mem_map_iff_mem hκi).mp h1
  have hta : ∀ t ∈ Tv, t * a * t⁻¹ = a := by
    intro t ht
    have hz : t * z * t⁻¹ = z := c.conj_z h1222 t (c.hyp.normalizes ht.1)
    suffices key : ∀ b ∈ Subgroup.closure ({v', q', z'} : Set ↥V), t * (b : G) * t⁻¹ = b from
      key a₀ hmemcl
    intro b hb
    induction hb using Subgroup.closure_induction with
    | mem b hb =>
      rcases hb with rfl | rfl | rfl
      · exact hcv t ht.2
      · exact htq t ht
      · exact hz
    | one => simp
    | mul b₁ b₂ _ _ ih₁ ih₂ =>
      rw [Subgroup.coe_mul]
      calc t * ((b₁ : G) * b₂) * t⁻¹ = (t * b₁ * t⁻¹) * (t * b₂ * t⁻¹) := by group
        _ = b₁ * b₂ := by rw [ih₁, ih₂]
    | inv b _ ih =>
      rw [Subgroup.coe_inv]
      calc t * (b : G)⁻¹ * t⁻¹ = (t * b * t⁻¹)⁻¹ := by group
        _ = (b : G)⁻¹ := by rw [ih]
  have haC : a ∈ Subgroup.centralizer (Tv : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    calc t * a = t * a * t⁻¹ * t := by group
      _ = a * t := by rw [hta t ht]
  refine ⟨a, haV, haC, x * a, Tv.mul_mem hxT (hVTv haV), Subgroup.mul_mem _ hxC haC, hbL, hdec⟩

end Cfg

end Lem26A8

open Lem26A8 in
theorem lem12216A8VvFix_of
    (h1222 : Stmt12_2_2) (h3228 : Stmt3_2_2_eight) :
    Lem12216A8VvFix := by
  intro G _ _ T L V z v g hH hNE hmod hVL hz1 hNV hvV hvz hgM hgv hsyl hgN hcomm x hxT hxC hx2
  obtain ⟨hcommV, hreal⟩ := hmod
  have c : Cfg T L V z v g :=
    ⟨hH, hNE, hcommV, hreal, hVL, hz1, hNV, hvV, hvz, hgM, hgv, hsyl, hgN⟩
  exact c.exists_decomp h1222 h3228 hcomm hxT hxC hx2

end CFSG.Quasithin.H13
