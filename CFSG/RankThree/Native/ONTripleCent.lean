module

public import CFSG.RankThree.Native.ONTripleNorm
public import CFSG.RankThree.Native.ONSevenRestrict
public meta import CFSG.RankThree.Native.ONSevenRestrict
public import Certificates.Certificate8139
public import Certificates.Certificate8143
public import Certificates.Certificate8144
public import Certificates.Certificate8142
public import Certificates.Certificate2212
public import Certificates.Certificate2217
public import Certificates.Certificate3171
public import Certificates.Certificate9127
public import Certificates.Certificate9217
public import CFSG.Certificates.NativeSchreierCard
public meta import CFSG.Certificates.NativeSchreierCard
public import CFSG.Monster.B.Mathieu.SylowSound
public meta import CFSG.Monster.B.Mathieu.SylowSound
public import CFSG.RankThree.Native.ONSevenDefs
public meta import CFSG.RankThree.Native.ONSevenDefs

public noncomputable section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.ONSchreier CFSG.ONSchreier.Native Subgroup
open scoped commutatorElement Pointwise

attribute [local irreducible] dotProduct

@[expose] def betaPv :
    PON.Group ≃* Pv :=
  nonempty_equiv_PON.some.symm.trans onEquivPv

@[expose] def phiM :
    GM →* Pv :=
  betaPv.toMonoidHom.comp (piON.comp modelEquiv.symm.toMonoidHom)

theorem phiM_surjective :
    Function.Surjective phiM :=
  betaPv.surjective.comp (piON_surjective.comp modelEquiv.symm.surjective)

theorem modelEquiv_zF :
    modelEquiv zF = zG := by
  apply Subtype.ext
  rw [modelEquiv_apply, psiM_zF]
  rfl

theorem ker_phiM :
    phiM.ker = zpowers zG := by
  ext g
  rw [MonoidHom.mem_ker, phiM, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_piON,
    MulEquiv.coe_toMonoidHom, mem_zpowers_iff, mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← modelEquiv_zF, ← map_zpow, hk, MulEquiv.apply_symm_apply]
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, ← modelEquiv_zF, ← map_zpow, MulEquiv.symm_apply_apply]

theorem card_Pv' :
    Nat.card Pv = 460815505920 := by
  rw [← Nat.card_congr onEquivPv.toEquiv, CFSG.Sporadic.ON.card_ON_eq]

theorem phiM_zG :
    phiM zG = 1 := by
  rw [← MonoidHom.mem_ker, ker_phiM]
  exact mem_zpowers zG

abbrev tPv :
    Equiv.Perm (Fin N) := evalS [6]

theorem t_letters : plettersOK 7 [6] = true := by decide

theorem t_check :
    (onSevenArr [6])[0]! = 0 ∧ (onSevenGood (onSevenArr [6]) []).length = 90 ∧
    onSevenCount (onSevenArr [6]) = 36 ∧
    peq N (pcomp N (onSevenArr [6]) (pcomp N (onSevenArr [6]) (onSevenArr [6]))) (pid N) = true ∧
    peq N (onSevenArr [6]) (pid N) = false :=
  Certificates.certificate8139

theorem prep_t :
    PRep N (onSevenArr [6]) tPv := prep_onSevenArr t_letters

theorem t_x0 :
    tPv x0 = x0 := by
  apply Fin.ext
  rw [← prep_t x0]
  exact t_check.1

theorem t_cube :
    tPv ^ 3 = 1 := by
  have h := eq_of_peq (prep_pcomp prep_t (prep_pcomp prep_t prep_t)) prep_pid t_check.2.2.2.1
  rw [pow_succ, pow_succ, pow_one, mul_assoc]
  exact h

theorem t_ne_one :
    tPv ≠ 1 := by
  intro h
  have := (peq_iff prep_t prep_pid).2 h
  rw [t_check.2.2.2.2] at this
  exact Bool.false_ne_true this

theorem card_centralizer_t_le :
    Nat.card (centralizer {tPv} ⊓ Pv : Subgroup (Equiv.Perm (Fin N))) ≤ 3240 := by
  have h := card_centralizer_le_of_good prep_t (evalS_mem _) t_x0 (bad := [])
    (fun q hq => by simp at hq)
  rw [t_check.2.1, t_check.2.2.1] at h
  exact h

theorem P0G_inf_ker :
    P0G ⊓ phiM.ker = zpowers zG := by
  rw [ker_phiM]
  exact inf_eq_right.2 ((zpowers_le).2 ThreeQRel.x_mem)

theorem card_map_P0G :
    Nat.card (P0G.map phiM) = 81 := by
  have h := card_ker_mul_card_range (phiM.domRestrict P0G)
  have hr : (phiM.domRestrict P0G).range = P0G.map phiM := by
    ext y
    rw [MonoidHom.mem_range, mem_map]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have hk : Nat.card (phiM.domRestrict P0G).ker = 3 := by
    rw [MonoidHom.ker_domRestrict, show phiM.ker.subgroupOf P0G = (zpowers zG).subgroupOf P0G by
        rw [← P0G_inf_ker, Subgroup.inf_subgroupOf_left],
      Nat.card_congr (subgroupOfEquivOfLe ((zpowers_le).2 ThreeQRel.x_mem)).toEquiv,
      Nat.card_zpowers, relG.orderOf_x]
  rw [hr, hk, relG.card_threeQ] at h
  omega

theorem factorization_card_Pv :
    (Nat.card Pv).factorization 3 = 4 := by
  rw [card_Pv', show (460815505920 : ℕ) = 3 ^ 4 * 5689080320 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

@[expose] def P0Pv :
    Sylow 3 Pv :=
  Sylow.ofCard (P0G.map phiM) (by rw [card_map_P0G, factorization_card_Pv]; norm_num)

@[expose] def tP :
    Pv := ⟨tPv, evalS_mem _⟩

theorem tP_conj :
    ∃ h : Pv, h⁻¹ * tP * h = phiM (xG 0) := by
  have hp : IsPGroup 3 (zpowers tP) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (Subtype.ext (by simpa [tP] using t_cube))
      (fun h => t_ne_one (congrArg Subtype.val h))
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq Pv S P0Pv
  have htmem : u * tP * u⁻¹ ∈ (P0Pv : Subgroup Pv) := by
    have h1 : MulAut.conj u • tP ∈ MulAut.conj u • (S : Subgroup Pv) :=
      Subgroup.smul_mem_pointwise_smul _ _ _ (hS (mem_zpowers tP))
    rwa [← Sylow.coe_subgroup_smul, hu, MulAut.smul_def, MulAut.conj_apply] at h1
  obtain ⟨p, hp0, hpt⟩ := htmem
  have hpz : p ∉ zpowers zG := by
    intro hz
    rw [← ker_phiM, MonoidHom.mem_ker] at hz
    rw [hz] at hpt
    have : tP = 1 := by
      have := congrArg (fun y => u⁻¹ * y * u) hpt
      simp only [mul_one, inv_mul_cancel] at this
      rw [show u⁻¹ * (u * tP * u⁻¹) * u = tP by group] at this
      exact this.symm
    exact t_ne_one (congrArg Subtype.val this)
  obtain ⟨n, c, hn⟩ := exists_conj_x0 hp0 hpz
  refine ⟨u⁻¹ * phiM n, ?_⟩
  have h1 : phiM (n⁻¹ * p * n) = phiM (xG 0) := by
    rw [hn, map_mul, map_pow, phiM_zG, one_pow, mul_one]
  rw [map_mul, map_mul, map_inv, hpt] at h1
  rw [← h1]
  group

theorem card_centralizer_conj {X : Type*} [Group X] (a h : X) :
    Nat.card (centralizer {h⁻¹ * a * h}) = Nat.card (centralizer {a}) := by
  have e : (centralizer {h⁻¹ * a * h} : Subgroup X) = (centralizer {a}).map
      (MulAut.conj h⁻¹).toMonoidHom := by
    ext g
    simp only [mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    constructor
    · intro hg
      refine ⟨h * g * h⁻¹, ?_, by group⟩
      calc h * g * h⁻¹ * a = h * (g * (h⁻¹ * a * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * a * h) * g) * h⁻¹ := by rw [hg]
        _ = a * (h * g * h⁻¹) := by group
    · rintro ⟨y, hy, rfl⟩
      calc h⁻¹ * y * h * (h⁻¹ * a * h) = h⁻¹ * (y * a) * h := by group
        _ = h⁻¹ * (a * y) * h := by rw [hy]
        _ = h⁻¹ * a * h * (h⁻¹ * y * h) := by group
  rw [e, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]

theorem card_centralizer_tP_le :
    Nat.card (centralizer {tP} : Subgroup Pv) ≤ 3240 := by
  have hle : (centralizer {tP} : Subgroup Pv).map Pv.subtype ≤ centralizer {tPv} ⊓ Pv := by
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, g.2⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hg
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hg
  rw [← Subgroup.card_map_of_injective Pv.subtype_injective]
  exact (Subgroup.card_le_of_le hle).trans card_centralizer_t_le

theorem comm_x0_x3 :
    ⁅xG 0, xG 3⁆ = zG := by
  rw [relG.comm, omegaZ_val, show omegaN (0 : Fin 4) (3 : Fin 4) = 1 by decide, pow_one]

theorem comm_x0_x3_pow
    (m : ℕ) : ⁅xG 0, xG 3 ^ m⁆ = zG ^ m := by
  rw [commutator_pow_right_of_commute (by rw [comm_x0_x3]; exact zG_central _), comm_x0_x3]

theorem phiM_x0_x3_comm :
    phiM (xG 0) * phiM (xG 3) = phiM (xG 3) * phiM (xG 0) := by
  have h : phiM ⁅xG 0, xG 3⁆ = 1 := by rw [comm_x0_x3, phiM_zG]
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem card_centralizer_phi_x0_le :
    Nat.card (centralizer {phiM (xG 0)} : Subgroup Pv) ≤ 3240 := by
  obtain ⟨h, hh⟩ := tP_conj
  rw [← hh, card_centralizer_conj]
  exact card_centralizer_tP_le

theorem card_centralizer_x0_le :
    Nat.card (centralizer {xG 0} : Subgroup GM) ≤ 3240 := by
  set D : Subgroup Pv := centralizer {phiM (xG 0)}
  set C : Subgroup GM := centralizer {xG 0}
  set Ch : Subgroup GM := D.comap phiM
  have hidx : Ch.index = D.index := Subgroup.index_comap_of_surjective D phiM_surjective
  have h1 := Ch.card_mul_index
  have h2 := D.card_mul_index
  rw [card_GM] at h1
  rw [card_Pv'] at h2
  have hD : Nat.card D ≤ 3240 := card_centralizer_phi_x0_le
  have hCh : Nat.card Ch = 3 * Nat.card D := by
    have hpos : 0 < D.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hidx] at h1
    nlinarith
  have hmem : ∀ (c : C) (k : Fin 3), (c : GM) * xG 3 ^ k.val ∈ Ch := by
    intro c k
    rw [Subgroup.mem_comap, mem_centralizer_singleton_iff, map_mul, map_pow]
    have hc : phiM c * phiM (xG 0) = phiM (xG 0) * phiM c := by
      rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.1 c.2)]
    have h3 : Commute (phiM (xG 3) ^ k.val) (phiM (xG 0)) :=
      (Commute.pow_left (phiM_x0_x3_comm).symm _)
    rw [mul_assoc, h3.eq, ← mul_assoc, hc, mul_assoc]
  let f : C × Fin 3 → Ch := fun p => ⟨p.1 * xG 3 ^ p.2.val, hmem p.1 p.2⟩
  have hf : Function.Injective f := by
    rintro ⟨c, k⟩ ⟨c', k'⟩ hcc
    have e : (c : GM) * xG 3 ^ k.val = c' * xG 3 ^ k'.val := congrArg Subtype.val hcc
    have key : ∀ {a b : Fin 3} {u v : C}, (u : GM) * xG 3 ^ a.val = v * xG 3 ^ b.val →
        a.val ≤ b.val → a = b ∧ u = v := by
      intro a b u v huv hab
      have hpow : xG 3 ^ (b.val - a.val) = (v : GM)⁻¹ * u := by
        have : xG 3 ^ b.val = xG 3 ^ a.val * xG 3 ^ (b.val - a.val) := by
          rw [← pow_add, Nat.add_sub_cancel' hab]
        rw [this] at huv
        calc xG 3 ^ (b.val - a.val) = (v : GM)⁻¹ * (v * (xG 3 ^ a.val * xG 3 ^ (b.val - a.val))) *
            (xG 3 ^ a.val)⁻¹ := by
              rw [show (v : GM)⁻¹ * (v * (xG 3 ^ a.val * xG 3 ^ (b.val - a.val))) *
                (xG 3 ^ a.val)⁻¹ = xG 3 ^ a.val * xG 3 ^ (b.val - a.val) * (xG 3 ^ a.val)⁻¹ by
                group]
              rw [← pow_add, ← pow_sub _ (Nat.le_add_right _ _)]
              congr 1
              omega
          _ = (v : GM)⁻¹ * u := by rw [← huv]; group
      have hcent : xG 3 ^ (b.val - a.val) ∈ C := by
        rw [hpow]
        exact C.mul_mem (C.inv_mem v.2) u.2
      have hz : zG ^ (b.val - a.val) = 1 := by
        rw [← comm_x0_x3_pow, commutatorElement_eq_one_iff_mul_comm]
        exact (mem_centralizer_singleton_iff.1 hcent).symm
      have hlt : b.val - a.val < 3 := by omega
      have h0 : b.val - a.val = 0 := by
        by_contra hne
        have hord := relG.orderOf_x
        have := orderOf_le_of_pow_eq_one (Nat.pos_of_ne_zero hne) hz
        omega
      have hab' : a = b := Fin.ext (by omega)
      subst hab'
      refine ⟨rfl, ?_⟩
      apply Subtype.ext
      exact mul_right_cancel huv
    rcases le_total k.val k'.val with h | h
    · obtain ⟨rfl, rfl⟩ := key e h
      rfl
    · obtain ⟨rfl, rfl⟩ := key e.symm h
      rfl
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, hCh] at hle
  omega

end CFSG.RankThree.Native.ONTriple
