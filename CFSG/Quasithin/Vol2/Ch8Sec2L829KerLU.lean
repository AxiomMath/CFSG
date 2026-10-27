module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829FelemL3M22
public import CFSG.Quasithin.Vol2.Ch8Sec2L829KerLUTransfer
public import CFSG.Quasithin.Vol2.Ch8Sec2L829KerLUHom

public section

namespace CFSG.Quasithin.H13

open CFSG.Open
open scoped IsMulCommutative commutatorElement

theorem simple_card_of_alternatingNatural_klu {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (h5 : AlternatingNatural H ⊤ ⊥ 5) (hH : H ≠ ⊥) :
    Finite ↥H ∧ IsSimpleGroup ↥H ∧ Nat.card ↥H = 60 := by
  obtain ⟨π₀, hπs, -⟩ := h5
  let π : ↥(alternatingGroup (Fin 5)) →* ↥H := π₀
  have hπs' : Function.Surjective π := hπs
  have hinj : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff π).mp hk
    · exfalso
      apply hH
      rw [eq_bot_iff]
      intro b hb
      obtain ⟨a, ha⟩ := hπs' ⟨b, hb⟩
      have hak : a ∈ π.ker := by
        rw [hk]
        exact Subgroup.mem_top a
      rw [MonoidHom.mem_ker, ha] at hak
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hak
  let e : alternatingGroup (Fin 5) ≃* ↥H := MulEquiv.ofBijective π ⟨hinj, hπs'⟩
  have hcardA : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hcardH : Nat.card ↥H = 60 := by
    rw [← Nat.card_congr e.toEquiv, hcardA]
  exact ⟨Finite.of_equiv _ e.toEquiv, MulEquiv.isSimpleGroup e.symm, hcardH⟩

theorem mem_pCore_of_mem_pCoreOf_klu {G : Type} [Group G] (L : Subgroup G) (p : ℕ) (y : ↥L)
    (hy : (y : G) ∈ pCoreOf p L) : y ∈ CFSG.pCore p ↥L := by
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  have hzy' : z = y := Subtype.ext hzy
  rw [← hzy']
  exact hz

theorem stmtKerLUOdd_holds (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal)
    (h825 : Stmt8_2_5) (hLU : HLU82) (hcard : CFSG.Quasithin.H.Mathieu.StmtH13Card)
    (h828 : Stmt8_2_8) : StmtKerLUOdd := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hrow' x hxLU hxC p hpm hxp
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hcomm := (h828 G T L I hyp h731 h821 hc hrow H h k hH hh hC).2.1
  obtain ⟨hV, hL0, -, hLN, -, hAN, hAL, hAp, hAe, -, -, -, -⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨-, h5, -, -⟩ := hlu82_82 hLU hcard hrow hL0 hV hLN hC5 hAN hAL hAp hAe
  have hA5 := h5 (hrow'.imp (fun hr => ⟨1, hr⟩) id)
  have hH0 := ne_bot_of_alternatingNatural_828 (Or.inl rfl) hA5
  set U := ch82U (fsuV T I) h with hUdef
  set LU := ch82LU L U with hLUdef
  set F := fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) with hFdef
  have hfix : F = U.subgroupOf (fsuV T I) := fixV_autOn_82 hAN
  have hUV : U ≤ fsuV T I := inf_le_left
  have hF : ∀ v : ↥(fsuV T I), v ∈ F ↔ (v : G) ∈ U := by
    intro v
    rw [hfix, Subgroup.mem_subgroupOf]
  have hLNV : LU ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    (perfectCore_le _).trans (inf_le_left.trans hLN)
  have hLNU : LU ≤ Subgroup.normalizer (U : Set G) :=
    (perfectCore_le _).trans inf_le_right
  obtain ⟨Φ0, hΦmem, hΦsurj, hΦker⟩ :=
    autSub_hom_klu (fsuV T I) LU U F hUV hF hLNV hLNU
  set Hs := autSub (autOn LU (fsuV T I)) F with hHsdef
  obtain ⟨hHsfin, hHssimple, hHscard⟩ := simple_card_of_alternatingNatural_klu hA5 hH0
  haveI : Finite ↥Hs := hHsfin
  haveI : IsSimpleGroup ↥Hs := hHssimple
  let Φ : ↥LU →* ↥Hs := Φ0.codRestrict Hs hΦmem
  have hΦsurj' : Function.Surjective Φ := by
    intro y
    obtain ⟨x', hx'⟩ := hΦsurj y.1 y.2
    exact ⟨x', Subtype.ext hx'⟩
  have hΦ1 : ∀ y : ↥LU, Φ y = 1 ↔ (y : G) ∈ Subgroup.centralizer (U : Set G) := by
    intro y
    rw [← hΦker y]
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact this
    · intro h
      exact Subtype.ext h
  haveI : Group.IsPerfect ↥LU :=
    Subgroup.isPerfect_iff.mpr (perfectCore_perfect (L ⊓ Subgroup.normalizer (U : Set G)))
  have hcent : ∀ g k : ↥LU, Φ k = 1 → ⁅g, k⁆ ∈ CFSG.pCore 2 ↥LU := by
    intro g k hk
    have hk' : (k : G) ∈ Subgroup.centralizer (U : Set G) := (hΦ1 k).mp hk
    have hcm : ⁅(g : G), (k : G)⁆ ∈ pCoreOf 2 LU :=
      hcomm (Subgroup.commutator_mem_commutator g.2 hk')
    apply mem_pCore_of_mem_pCoreOf_klu LU 2 ⁅g, k⁆
    have e : (((⁅g, k⁆ : ↥LU)) : G) = ⁅(g : G), (k : G)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact hcm
  have hxLU' : x ∈ LU := hxLU
  have hΦx : Φ ⟨x, hxLU'⟩ = 1 := (hΦ1 ⟨x, hxLU'⟩).mpr hxC
  have hxp' : (⟨x, hxLU'⟩ : ↥LU) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact hxp
  have key := eq_one_of_perfect_ext_klu (CFSG.pCore 2 ↥LU) (CFSG.pCore_isPGroup) hHscard Φ
    hΦsurj' hcent hpm ⟨x, hxLU'⟩ hΦx hxp'
  have := congrArg Subtype.val key
  simpa using this

end CFSG.Quasithin.H13
