module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Quot

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open
open scoped commutatorElement

theorem f3_quot_equiv_of_surj {L M : Type} [Group L] [Group M] [Finite L] [Finite M]
    (ψ : L →* M) (hψ : Function.Surjective ψ) (hker : IsPGroup 2 ψ.ker) :
    Nonempty (L ⧸ CFSG.pCore 2 L ≃* M ⧸ CFSG.pCore 2 M) := by
  obtain ⟨f, hf⟩ : ∃ f : L →* M ⧸ CFSG.pCore 2 M, ∀ x, f x = QuotientGroup.mk (ψ x) :=
    ⟨(QuotientGroup.mk' (CFSG.pCore 2 M)).comp ψ, fun x => rfl⟩
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := hψ m
    exact ⟨x, hf x⟩
  have hkey : f.ker = CFSG.pCore 2 L := by
    apply le_antisymm
    ·
      have hkp : IsPGroup 2 f.ker := by
        intro x
        have hx : ψ (x : L) ∈ CFSG.pCore 2 M := by
          have hxk := x.2
          rw [MonoidHom.mem_ker, hf, QuotientGroup.eq_one_iff] at hxk
          exact hxk
        obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := M)) ⟨ψ (x : L), hx⟩
        have hj' : ψ ((x : L) ^ 2 ^ j) = 1 := by
          rw [map_pow]
          exact congrArg Subtype.val hj
        obtain ⟨i, hi⟩ := hker ⟨(x : L) ^ 2 ^ j, MonoidHom.mem_ker.mpr hj'⟩
        refine ⟨j + i, Subtype.ext ?_⟩
        show (x : L) ^ 2 ^ (j + i) = 1
        calc (x : L) ^ 2 ^ (j + i) = ((x : L) ^ 2 ^ j) ^ 2 ^ i := by
              rw [← pow_mul, ← pow_add]
          _ = 1 := congrArg Subtype.val hi
      exact le_sSup ⟨inferInstance, hkp⟩
    ·
      intro x hx
      rw [MonoidHom.mem_ker, hf, QuotientGroup.eq_one_iff]
      have hsub : (CFSG.pCore 2 L).map ψ ≤ CFSG.pCore 2 M := by
        apply le_sSup
        exact ⟨Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := L)) ψ hψ,
          IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := L)) ψ⟩
      exact hsub (Subgroup.mem_map_of_mem ψ hx)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkey.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hfsurj)⟩

theorem f3_isPSL_modO2 {G : Type} [Group G] [Finite G] {H L : Subgroup G} (hLH : L ≤ H)
    {n p e : ℕ} (h : IsPSL n p e (↥L ⧸ CFSG.pCore 2 ↥L)) :
    IsPSL n p e (↥(CFSG.Quasithin.modO2Image H L) ⧸ CFSG.pCore 2 ↥(CFSG.Quasithin.modO2Image H L)) := by
  obtain ⟨ψ, hsurj, hker⟩ :=
    CFSG.QuasithinUnique.Unc25G2.A312Sub.exists_modO2_surjection_of_le hLH
  obtain ⟨φ⟩ := f3_quot_equiv_of_surj ψ hsurj hker
  exact IsPSL.of_mulEquiv φ h

theorem f3_isPSL_conj {G : Type} [Group G] [Finite G] (K : Subgroup G) (t : G) {n p e : ℕ}
    (h : IsPSL n p e (↥K ⧸ CFSG.pCore 2 ↥K)) :
    IsPSL n p e (↥(K.map (MulAut.conj t).toMonoidHom) ⧸
      CFSG.pCore 2 ↥(K.map (MulAut.conj t).toMonoidHom)) := by
  let e' : ↥K ≃* ↥(K.map (MulAut.conj t).toMonoidHom) :=
    MulEquiv.subgroupMap (MulAut.conj t) K
  have hker : IsPGroup 2 (e'.toMonoidHom).ker := by
    rw [(MonoidHom.ker_eq_bot_iff e'.toMonoidHom).mpr e'.injective]
    exact IsPGroup.of_bot
  obtain ⟨φ⟩ := f3_quot_equiv_of_surj e'.toMonoidHom e'.surjective hker
  exact IsPSL.of_mulEquiv φ h

end CFSG.Quasithin.H13.NF314pt
