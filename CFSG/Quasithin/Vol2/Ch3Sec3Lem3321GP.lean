module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321WH
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GW

public section

namespace CFSG.Quasithin.H13.L3321

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Lift CFSG.Quasithin.S152N
open CFSG.Open (pCoreOf)

section Psi

variable {G : Type} [Group G] {L T : Subgroup G} {α : ↥L →* SL4}

theorem exists_psiH [Finite G] (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (hU : ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4) (hout : ¬ InducesInnerOn T L) :
    ∃ ψ : ↥(L3316.liftPre α P2 ⊔ T) →* W3, Function.Surjective ψ ∧
      ψ.ker = CFSG.pCore 2 ↥(L3316.liftPre α P2 ⊔ T) ∧
      ∀ (x : G) (hxH : x ∈ L3316.liftPre α P2 ⊔ T) (hxN : x ∈ Subgroup.normalizer (L : Set G))
        (gk : Pgam), indAut hα hker ⟨x, hxN⟩ = xiHom gk → ψ ⟨x, hxH⟩ = chiHom gk := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := L3316.liftPre α P2 with hPdef
  set H := P ⊔ T with hHdef
  have hPL : P ≤ L := L3316.liftPre_le α P2
  have hHN : H ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (hPL.trans Subgroup.le_normalizer) hTL
  have hHLT : H ≤ L ⊔ T := sup_le_sup_right hPL T
  set Φ : ↥H →* MulAut SL4 := (indAut hα hker).comp (Subgroup.inclusion hHN) with hΦ
  have hrange : ∀ h : ↥H, Φ h ∈ xiHom.range := by
    let K : Subgroup G := (xiHom.range.comap (indAut hα hker)).map
      (Subgroup.normalizer (L : Set G)).subtype
    have hPK : P ≤ K := by
      rintro _ ⟨l, hl, rfl⟩
      refine ⟨⟨l, Subgroup.le_normalizer l.2⟩, ?_, rfl⟩
      show indAut hα hker ⟨l, Subgroup.le_normalizer l.2⟩ ∈ xiHom.range
      rw [indAut_of_mem]
      refine ⟨⟨⟨α l, hl⟩, 1⟩, ?_⟩
      rw [xiHom_mk, map_one, mul_one]
    have hTK : T ≤ K := by
      intro t ht
      refine ⟨⟨t, hTL ht⟩, ?_, rfl⟩
      obtain ⟨u, hu, k, hk⟩ := exists_xiHom_of_map_Ut _ (map_Ut_indAut hα hker hTL hU ht)
      exact ⟨_, hk.symm⟩
    intro h
    obtain ⟨y, hy, hyh⟩ := (sup_le hPK hTK) h.2
    have e : (y : ↥(Subgroup.normalizer (L : Set G))) = Subgroup.inclusion hHN h :=
      Subtype.ext hyh
    show indAut hα hker (Subgroup.inclusion hHN h) ∈ xiHom.range
    rw [← e]
    exact hy
  set e := MonoidHom.ofInjective xiHom_injective with he
  set ψ : ↥H →* W3 :=
    chiHom.comp (e.symm.toMonoidHom.comp (Φ.codRestrict xiHom.range hrange)) with hψ
  have hψ_eq : ∀ (h : ↥H) (gk : Pgam), Φ h = xiHom gk → ψ h = chiHom gk := by
    intro h gk hgk
    have h1 : e gk = Φ.codRestrict xiHom.range hrange h := Subtype.ext hgk.symm
    show chiHom (e.symm (Φ.codRestrict xiHom.range hrange h)) = chiHom gk
    rw [← h1, MulEquiv.symm_apply_apply]
  have hT1 : ∃ (t : G) (ht : t ∈ T) (u : SL4) (hu : u ∈ FLc.Ut 4),
      indAut hα hker ⟨t, hTL ht⟩ = xiHom ⟨⟨u, Ut_le_P2 hu⟩, Multiplicative.ofAdd 1⟩ := by
    by_contra hno
    apply hout
    intro t ht
    obtain ⟨u, hu, k, hk⟩ := exists_xiHom_of_map_Ut _ (map_Ut_indAut hα hker hTL hU ht)
    rcases mult_z2_cases k with rfl | rfl
    · rw [xiHom_mk, map_one, mul_one] at hk
      obtain ⟨y, hy⟩ := hα u
      refine ⟨y, y.2, fun x hx => ?_⟩
      have hxt := (Subgroup.mem_normalizer_iff.mp (hTL ht) x).mp hx
      have h1 : α ⟨t * x * t⁻¹, hxt⟩ = α (y * ⟨x, hx⟩ * y⁻¹) := by
        have h2 := indAut_apply hα hker ⟨t, hTL ht⟩ ⟨x, hx⟩
        rw [hk, MulAut.conj_apply] at h2
        rw [map_mul, map_mul, map_inv, hy]
        exact h2.symm
      have h3 : (⟨t * x * t⁻¹, hxt⟩ : ↥L) * (y * ⟨x, hx⟩ * y⁻¹)⁻¹ ∈ CFSG.pCore 2 ↥L := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
      exact (Lem3328.mem_pCore_iff _).1 h3
    · exact absurd ⟨t, ht, u, hu, hk⟩ hno
  obtain ⟨t₀, ht₀, u₀, hu₀, hk₀⟩ := hT1
  have ht₀H : t₀ ∈ H := Subgroup.mem_sup_right ht₀
  have hψt₀ : ψ ⟨t₀, ht₀H⟩ = chiHom ⟨⟨u₀, Ut_le_P2 hu₀⟩, Multiplicative.ofAdd 1⟩ :=
    hψ_eq _ _ hk₀
  have hbase : ∀ w : W3, w.right = 1 → ∃ h : ↥H, ψ h = w := by
    intro w hw
    obtain ⟨⟨g, k⟩, hgk⟩ := chiHom_surjective w
    have hk : k = 1 := by
      have h1 : (baseW (betaB g) * RegularWreathProduct.inl k).right = 1 := by
        rw [← chiHom_mk, hgk, hw]
      rwa [RegularWreathProduct.mul_right, RegularWreathProduct.right_inl,
        show (baseW (betaB g)).right = 1 from rfl, one_mul] at h1
    subst hk
    obtain ⟨l, hl⟩ := hα (g : SL4)
    have hlP : (l : G) ∈ P := ⟨l, show α l ∈ P2 by rw [hl]; exact g.2, rfl⟩
    refine ⟨⟨l, Subgroup.mem_sup_left hlP⟩, ?_⟩
    rw [← hgk]
    refine hψ_eq _ _ ?_
    show indAut hα hker ⟨l, _⟩ = _
    rw [indAut_of_mem, xiHom_mk, map_one, mul_one, hl]
  have hψs : Function.Surjective ψ := by
    intro w
    rcases mult_z2_cases w.right with hw | hw
    · exact hbase w hw
    · have hr : (ψ ⟨t₀, ht₀H⟩).right = Multiplicative.ofAdd 1 := by
        rw [hψt₀, chiHom_mk, RegularWreathProduct.mul_right, RegularWreathProduct.right_inl,
          show (baseW (betaB ⟨u₀, Ut_le_P2 hu₀⟩)).right = 1 from rfl, one_mul]
      obtain ⟨h, hh⟩ := hbase (w * (ψ ⟨t₀, ht₀H⟩)⁻¹) (by
        rw [RegularWreathProduct.mul_right, RegularWreathProduct.inv_right, hr, hw,
          mul_inv_cancel])
      exact ⟨h * ⟨t₀, ht₀H⟩, by rw [map_mul, hh, inv_mul_cancel_right]⟩
  have hker2 : IsPGroup 2 ψ.ker := by
    rintro ⟨h, hh⟩
    have hh' : ψ h = 1 := hh
    obtain ⟨⟨g, k⟩, hgk⟩ : ∃ gk : Pgam, e gk = Φ.codRestrict xiHom.range hrange h :=
      ⟨_, e.apply_symm_apply _⟩
    have hxi : xiHom ⟨g, k⟩ = Φ h := by
      have h1 : ((e ⟨g, k⟩ : ↥xiHom.range) : MulAut SL4) =
          ((Φ.codRestrict xiHom.range hrange h : ↥xiHom.range) : MulAut SL4) :=
        congrArg Subtype.val hgk
      rw [he, MonoidHom.ofInjective_apply] at h1
      exact h1
    have hchi : chiHom ⟨g, k⟩ = 1 := by rw [← hψ_eq h _ hxi.symm, hh']
    obtain ⟨hk1, hgU⟩ := chiHom_eq_one hchi
    have hΦh : Φ h = MulAut.conj (g : SL4) := by rw [← hxi, xiHom_mk, hk1, map_one, mul_one]
    obtain ⟨a, ha⟩ := (SzN2.isSylowTwoOf_unitriangular (K := ZMod 2) (n := 4)
      (by norm_num)).2.1 ⟨g, hgU⟩
    have ha' : (g : SL4) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hΦ2 : indAut hα hker (Subgroup.inclusion hHN (h ^ 2 ^ a)) = 1 := by
      rw [map_pow, map_pow]
      show (Φ h) ^ 2 ^ a = 1
      rw [hΦh, ← map_pow, ha', map_one]
    obtain ⟨b, hb⟩ := exists_pow_eq_one_of_indAut hα hker hT2 hTL _ (hHLT (h ^ 2 ^ a).2) hΦ2
    refine ⟨a + b, Subtype.ext (Subtype.ext ?_)⟩
    have hb' : ((h : G) ^ 2 ^ a) ^ 2 ^ b = 1 := hb
    show (h : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul, hb']
  have hle1 : ψ.ker ≤ CFSG.pCore 2 ↥H := le_sSup ⟨MonoidHom.normal_ker ψ, hker2⟩
  have hle2 : CFSG.pCore 2 ↥H ≤ ψ.ker := by
    have hN : ((CFSG.pCore 2 ↥H).map ψ).Normal :=
      (CFSG.pCore_normal (p := 2) (G := ↥H)).map ψ hψs
    have h2 : IsPGroup 2 ((CFSG.pCore 2 ↥H).map ψ) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map ψ
    have hbot := W3.normal_isPGroup_eq_bot hN h2
    intro x hx
    rw [MonoidHom.mem_ker]
    have : ψ x ∈ (CFSG.pCore 2 ↥H).map ψ := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact ⟨ψ, hψs, le_antisymm hle1 hle2, fun x hxH hxN gk hgk => hψ_eq ⟨x, hxH⟩ gk hgk⟩

end Psi

theorem chiHom_left (g : ↥P2) (k : Multiplicative (ZMod 2)) :
    (chiHom ⟨g, k⟩).left = betaB g := by
  rw [chiHom_mk]
  funext x
  simp [baseW, RegularWreathProduct.mul_def, RegularWreathProduct.left_inl]

theorem chiHom_right (g : ↥P2) (k : Multiplicative (ZMod 2)) : (chiHom ⟨g, k⟩).right = k := by
  rw [chiHom_mk, RegularWreathProduct.mul_right, RegularWreathProduct.right_inl,
    show (baseW (betaB g)).right = 1 from rfl, one_mul]

@[expose] def trN : SL2F2 := ⟨!![1, 1; 0, 1], by decide⟩

theorem sl2_cases : ∀ A : SL2F2,
    (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) 1 0 = 0 → A = 1 ∨ A = trN := by
  decide

theorem trN_mul_self : trN * trN = 1 := by decide

theorem trN_ne_one : trN ≠ 1 := by decide

@[expose] noncomputable def tau0 : Equiv.Perm (Fin 3) := sl2F2EquivPerm3 trN

theorem tau0_mul_self : tau0 * tau0 = 1 := by
  rw [tau0, ← map_mul, trN_mul_self, map_one]

theorem tau0_ne_one : tau0 ≠ 1 := fun h =>
  trN_ne_one (sl2F2EquivPerm3.injective (h.trans (map_one sl2F2EquivPerm3).symm))

theorem chiHom_left_mem {u : SL4} (hu : u ∈ FLc.Ut 4) (k : Multiplicative (ZMod 2))
    (q : Multiplicative (ZMod 2)) :
    (chiHom ⟨⟨u, Ut_le_P2 hu⟩, k⟩).left q = 1 ∨ (chiHom ⟨⟨u, Ut_le_P2 hu⟩, k⟩).left q = tau0 := by
  rw [chiHom_left]
  have hlow := (mem_unitriangular.1 hu).1
  have hA : blkA ⟨u, Ut_le_P2 hu⟩ = 1 ∨ blkA ⟨u, Ut_le_P2 hu⟩ = trN := by
    apply sl2_cases
    rw [coe_blkA, blkAM_apply]
    exact hlow _ _ (by decide)
  have hC : blkC ⟨u, Ut_le_P2 hu⟩ = 1 ∨ blkC ⟨u, Ut_le_P2 hu⟩ = trN := by
    apply sl2_cases
    rw [coe_blkC, blkCM_apply]
    exact hlow _ _ (by decide)
  show (if q = 1 then sl2F2EquivPerm3 (blkA ⟨u, Ut_le_P2 hu⟩)
      else sl2F2EquivPerm3 (blkC ⟨u, Ut_le_P2 hu⟩)) = 1 ∨
    (if q = 1 then sl2F2EquivPerm3 (blkA ⟨u, Ut_le_P2 hu⟩)
      else sl2F2EquivPerm3 (blkC ⟨u, Ut_le_P2 hu⟩)) = tau0
  by_cases hq : q = 1
  · rw [ite_eq_left hq]
    rcases hA with h | h <;> rw [h]
    · exact Or.inl (map_one _)
    · exact Or.inr rfl
  · rw [ite_eq_right hq]
    rcases hC with h | h <;> rw [h]
    · exact Or.inl (map_one _)
    · exact Or.inr rfl

theorem diagSL_trN_mem : diagSL trN 1 ∈ FLc.Ut 4 := by
  rw [mem_unitriangular]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd hij (by decide)
      | rfl
  · fin_cases i <;> rfl

theorem chiHom_diagSL :
    chiHom ⟨⟨diagSL trN 1, diagSL_mem trN 1⟩, 1⟩ = W3D.sW tau0 := by
  apply RegularWreathProduct.ext
  · rw [chiHom_left]
    funext q
    show (if q = 1 then sl2F2EquivPerm3 (blkA ⟨diagSL trN 1, diagSL_mem trN 1⟩)
      else sl2F2EquivPerm3 (blkC ⟨diagSL trN 1, diagSL_mem trN 1⟩)) =
        (if q = 1 then tau0 else 1)
    rw [blkA_diagSL, blkC_diagSL, map_one]
    rfl
  · rw [chiHom_right]
    rfl

section Inner

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G} {α : ↥L →* SL4}

@[expose] def conjEnd (d : G) (hd : d ∈ Subgroup.normalizer (T : Set G)) : Monoid.End ↥T where
  toFun x := ⟨d * x * d⁻¹, (Subgroup.mem_normalizer_iff.mp hd x).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

omit [Finite G] in
theorem conjEnd_pow (d : G) (hd : d ∈ Subgroup.normalizer (T : Set G)) (k : ℕ) (x : ↥T) :
    (((conjEnd d hd ^ k) x : ↥T) : G) = d ^ k * x * (d ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    show d * (((conjEnd d hd ^ k) x : ↥T) : G) * d⁻¹ = _
    rw [ih, pow_succ']
    group

theorem inf_le_pCoreOf : pCoreOf 2 (L ⊔ T) ⊓ L ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right (fun l hl => ?_)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_inf_left
  exact ChiefCount.mem_normalizer_inf
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl))
    (Subgroup.le_normalizer hl)

end Inner

end CFSG.Quasithin.H13.L3321
