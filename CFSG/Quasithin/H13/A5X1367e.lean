module

public import CFSG.Quasithin.H13.A5X1367d
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative commutatorElement

section ModuleFacts

variable {U : Type} [CommGroup U]

theorem fixV_apply_of_normalizer {J : Subgroup (MulAut U)} {g : MulAut U}
    (hg : g ∈ Subgroup.normalizer (J : Set (MulAut U))) {w : U} (hw : w ∈ fixV J) :
    g w ∈ fixV J :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hg hw

theorem commV_apply_of_normalizer {J : Subgroup (MulAut U)} {g : MulAut U}
    (hg : g ∈ Subgroup.normalizer (J : Set (MulAut U))) {u : U} (hu : u ∈ commV J) :
    g u ∈ commV J :=
  CFSG.Quasithin.commV_apply_mem_of_mem_normalizer hg hu

end ModuleFacts

theorem le_pCoreOf_of_le_abelian {Γ : Type} [Group Γ] [Finite Γ] {Z H P : Subgroup Γ}
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZH : Z ≤ H)
    (hHZ : H ≤ Subgroup.normalizer (Z : Set Γ)) (hP : IsPGroup 2 P) (hPZ : P ≤ Z) :
    P ≤ pCoreOf 2 H := by
  set Q : Subgroup Γ :=
    { carrier := {x | x ∈ Z ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}
      one_mem' := ⟨Z.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, k, hk⟩ ⟨hb, l, hl⟩
        refine ⟨Z.mul_mem ha hb, k + l, ?_⟩
        have e : (2 : ℕ) ^ (k + l) = 2 ^ k * 2 ^ l := pow_add 2 k l
        rw [Commute.mul_pow (hZc a ha b hb), e, pow_mul, hk, one_pow, one_mul,
          mul_comm (2 ^ k) (2 ^ l), pow_mul, hl, one_pow]
      inv_mem' := by
        rintro a ⟨ha, k, hk⟩
        exact ⟨Z.inv_mem ha, k, by rw [inv_pow, hk, inv_one]⟩ } with hQ
  have hQ2 : IsPGroup 2 Q := fun x => by
    obtain ⟨-, k, hk⟩ := x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hQH : Q ≤ H := fun x hx => hZH hx.1
  have hHQ : H ≤ Subgroup.normalizer (Q : Set Γ) := by
    intro h hh
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
    · obtain ⟨hxZ, k, hk⟩ := hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hHZ hh) x).mp hxZ, k, ?_⟩
      rw [conj_pow, hk]; group
    · obtain ⟨hxZ, k, hk⟩ := hx
      have hh' := hHZ (H.inv_mem hh)
      refine ⟨?_, k, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hh' x).mp hxZ
        simpa using this
      · have : (h⁻¹ * x * h) ^ 2 ^ k = h⁻¹ * x ^ 2 ^ k * h := by
          have := conj_pow (a := h⁻¹) (b := x) (i := 2 ^ k)
          simpa using this
        rw [this, hk]; group
  have hQO : Q ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQH hHQ hQ2
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  exact hQO ⟨hPZ hx, k, by simpa using congrArg Subtype.val hk⟩

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

@[expose] def GoodComp (K : Subgroup (MulAut ↥S.Uv)) : Prop :=
  IsComponentOf K (autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv) ∧
    autOn (thompsonJ S.Tv) S.Uv ≤ Subgroup.normalizer (K : Set (MulAut ↥S.Uv)) ∧
    ¬ autOn (thompsonJ S.Tv) S.Uv ≤ Subgroup.centralizer (K : Set (MulAut ↥S.Uv))

theorem isPGroup_JTS : IsPGroup 2 (autOn (thompsonJ S.Tv) S.Uv) := by
  have hJN : thompsonJ S.Tv ≤ Subgroup.normalizer (S.Uv : Set G) :=
    (B6.thompsonJ_le S.Tv).trans (S.Tv_le_Gv.trans S.Gv_le_normalizer_Uv)
  have hp : IsPGroup 2 (thompsonJ S.Tv) :=
    S.isPGroup_T.to_le ((B6.thompsonJ_le S.Tv).trans inf_le_left)
  exact (hp.of_equiv (Subgroup.subgroupOfEquivOfLe hJN).symm).map (conjAct S.Uv)

theorem commutator_self_le {Γ : Type} [Group Γ] (J : Subgroup Γ) : ⁅J, J⁆ ≤ J := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact J.mul_mem (J.mul_mem (J.mul_mem ha hb) (J.inv_mem ha)) (J.inv_mem hb)

theorem normalizer_le_normalizer_commutator {Γ : Type} [Group Γ] [Finite Γ] (J : Subgroup Γ) :
    Subgroup.normalizer (J : Set Γ) ≤ Subgroup.normalizer ((⁅J, J⁆ : Subgroup Γ) : Set Γ) := by
  have key : ∀ g ∈ Subgroup.normalizer (J : Set Γ), ∀ x ∈ ⁅J, J⁆, g * x * g⁻¹ ∈ ⁅J, J⁆ := by
    intro g hg x hx
    have hle : ⁅J, J⁆ ≤ (⁅J, J⁆).comap (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show g * ⁅a, b⁆ * g⁻¹ ∈ ⁅J, J⁆
      have e : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hg a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp hg b).mp hb)
    exact hle hx
  intro g hg
  refine B6.mem_normalizer_of_forall_mem (key g hg) fun x hx => ?_
  have := key g⁻¹ (Subgroup.inv_mem _ hg) x hx
  simpa using this

theorem false_of_case2 (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (hVv : ¬ Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G))
    {J : Subgroup (MulAut ↥S.Uv)}
    (hJG : J ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hGJ : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (J : Set (MulAut ↥S.Uv)))
    (h2 : haveI : IsMulCommutative ↥S.Uv := (S.elemAbelian_Uv h1222 h517 hF).1
      B56Case2 J) : False := by
  have hUe := S.elemAbelian_Uv h1222 h517 hF
  have : IsMulCommutative ↥S.Uv := hUe.1
  obtain ⟨⟨e⟩, ⟨hsup, hinf⟩, hcard⟩ := h2
  have hsq : ∀ a : ↥S.Uv, a * a = 1 := fun a => by
    have h := hUe.2 (a : G) a.2
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, h, Subgroup.coe_one])
  have hdec : ∀ u : ↥S.Uv, ∃ a ∈ commV J, ∃ w ∈ fixV J, u = a * w := by
    intro u
    have hu : u ∈ commV J ⊔ fixV J := by rw [hsup]; exact Subgroup.mem_top u
    obtain ⟨a, ha, w, hw, h⟩ := Subgroup.mem_sup.mp hu
    exact ⟨a, ha, w, hw, h.symm⟩
  set σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 with hσ
  set τ : Equiv.Perm (Fin 3) := Equiv.swap 1 2 with hτ
  set y₀ : MulAut ↥S.Uv := ⁅((e.symm σ : ↥J) : MulAut ↥S.Uv), ((e.symm τ : ↥J) : MulAut ↥S.Uv)⁆
    with hy₀
  have hy₀Y : y₀ ∈ ⁅J, J⁆ := Subgroup.commutator_mem_commutator (e.symm σ).2 (e.symm τ).2
  have hy₀J : y₀ = ((e.symm ⁅σ, τ⁆ : ↥J) : MulAut ↥S.Uv) := by
    rw [map_commutatorElement, hy₀]
    rfl
  have hy₀1 : y₀ ≠ 1 := by
    rw [hy₀J]
    intro h
    have h1 : e.symm ⁅σ, τ⁆ = 1 := Subtype.ext h
    have h2 : ⁅σ, τ⁆ = 1 := e.symm.injective (h1.trans (map_one e.symm).symm)
    exact absurd h2 (by decide)
  have hy₀3 : orderOf y₀ = 3 := by
    rw [hy₀J, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by decide) (by decide)
  have hy₀U : ∃ u ∈ commV J, y₀ u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hy₀1
    ext u
    obtain ⟨a, ha, w, hw, rfl⟩ := hdec u
    rw [map_mul, hcon a ha, (fixV J).mem_carrier.mp hw y₀ (commutator_self_le J hy₀Y),
      MulAut.one_apply]
  have hsylJ := A4.isSylowTwoOf_inf_normal (S.isSylowTwoOf_TvS h1222 h517) hJG hGJ
  have hJ6 : Nat.card ↥J = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  obtain ⟨s, hsTJ, hs1⟩ : ∃ s ∈ autOn S.Tv S.Uv ⊓ J, s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : autOn S.Tv S.Uv ⊓ J = ⊥ := eq_bot_iff.mpr fun x hx => hcon x hx
    have h : ¬ 2 ∣ (autOn S.Tv S.Uv ⊓ J).relIndex J := hsylJ.2.2
    rw [hbot, Subgroup.relIndex_bot_left, hJ6] at h
    exact h (by norm_num)
  have hsU : ∃ u ∈ commV J, s u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hs1
    ext u
    obtain ⟨a, ha, w, hw, rfl⟩ := hdec u
    rw [map_mul, hcon a ha, (fixV J).mem_carrier.mp hw s hsTJ.2, MulAut.one_apply]
  apply hVv
  refine S.le_normalizer_Vv_of_three hUe (Y := ⁅J, J⁆) ((commutator_self_le J).trans hJG)
    (hGJ.trans (normalizer_le_normalizer_commutator J))
    (fun h => hy₀1 ((Subgroup.mem_bot).mp (h ▸ hy₀Y))) hcard hdec hinf
    (fun y hy w hw => hw y (commutator_self_le J hy)) ?_
    (fun g hg u hu => commV_apply_of_normalizer (hGJ hg) hu)
    (fun g hg w hw => fixV_apply_of_normalizer (hGJ hg) hw) hsTJ.1
    (fun w hw => hw s hsTJ.2) hsU
  intro u hu hfix
  by_contra hu1
  have hy₀odd : Odd (orderOf y₀) := by rw [hy₀3]; decide
  exact four_odd_nofix hcard (fun e _ => hsq e)
    (fun x hx => commV_apply_of_normalizer (hGJ (hJG (commutator_self_le J hy₀Y))) hx)
    hy₀odd hy₀U hu hu1 (hfix y₀ hy₀Y)

end Setting

end CFSG.Quasithin.H13.A5
