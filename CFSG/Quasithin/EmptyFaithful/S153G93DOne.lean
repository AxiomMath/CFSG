module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.EmptyFaithful.S153EB6D
public import CFSG.Quasithin.Background.B69Red
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.Background.B5B42

public section

namespace CFSG.Quasithin

namespace S153G93D

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Hypotheses

variable {W : Type} [CommGroup W] [Finite W] {G₀ K S : Subgroup (MulAut W)} {a : MulAut W} {z : W}

theorem Ctx1.isQuasisimple (h : Ctx1 W G₀ K a S z) : CFSG.IsQuasisimple ↥K := by
  have := h.simple
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nab).1

theorem Ctx1.isIrrSec (h : Ctx1 W G₀ K a S z) : XMod.IsIrrSec ↥K (⊥ : Subgroup W) ⊤ := by
  have hnt : (⊤ : Subgroup W) ≠ ⊥ := h.irr.1
  exact ⟨bot_lt_iff_ne_bot.2 hnt, fun J hJ _ _ =>
    h.irr.2.2 J le_top (fun l hl u hu => hJ ⟨l, hl⟩ u hu)⟩

theorem Ctx1.normal_G₀ (h : Ctx1 W G₀ K a S z) : ∀ y ∈ G₀, ∀ l ∈ K, y * l * y⁻¹ ∈ K := by
  intro y hy l hl
  rcases h.mem_K_or_mul hy with hk | ⟨k, hk, rfl⟩
  · exact K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk)
  · have h1 : a * l * a⁻¹ ∈ K := h.aN l hl
    have e : k * a * l * (k * a)⁻¹ = k * (a * l * a⁻¹) * k⁻¹ := by group
    rw [e]
    exact K.mul_mem (K.mul_mem hk h1) (K.inv_mem hk)

theorem Ctx1.sq_mem (h : Ctx1 W G₀ K a S z) {y : MulAut W} (hy : y ∈ G₀) : y ^ 2 ∈ K := by
  rcases h.mem_K_or_mul hy with hk | ⟨k, hk, rfl⟩
  · exact K.pow_mem hk 2
  · have ha2 : a * a = 1 := by rw [← pow_two]; exact h.a2
    have e : (k * a) ^ 2 = k * (a * k * a⁻¹) * (a * a) := by rw [pow_two]; group
    rw [e, ha2, mul_one]
    exact K.mul_mem hk (h.aN k hk)

theorem Ctx1.quasithinGenFitting_eq (h : Ctx1 W G₀ K a S z) : quasithinGenFitting G₀ = K := by
  have hq : CFSG.Open.IsQuasisimple ↥K := A3.isQuasisimple_iff_open.mp h.isQuasisimple
  have hO2 : pCoreOf 2 G₀ = ⊥ := by
    refine S153EB6.pCoreOf_two_eq_bot_of_irr h.exp h.K_le fun B hB => ?_
    exact h.irr.2.2 B le_top hB
  exact InternalSec.quasithinGenFitting_eq_of_two_pow h.K_le h.normal_G₀ hq
    (fun y hy => ⟨1, by simpa using h.sq_mem hy⟩) hO2

theorem b4Hyp_of_ctx1 (hA21 : AsA21SQTKSection) {H : Subgroup (MulAut W)}
    (hq : G64.IsQuotientOfSQTKCat ↥H) (hKH : K ≤ H) (h : Ctx1 W G₀ K a S z) : B4Hyp G₀ K := by
  obtain ⟨Y, _, _, φ, hY, hφ⟩ : ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (φ : Y →* ↥H),
      SQTKGroup Y ∧ Function.Surjective φ := by
    obtain ⟨Y, _, _, N, _, hY, ⟨e⟩⟩ := hq
    exact ⟨Y, inferInstance, inferInstance,
      e.symm.toMonoidHom.comp (QuotientGroup.mk' N),
      ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mp hY.1, hY.2⟩,
      e.symm.surjective.comp (QuotientGroup.mk'_surjective N)⟩
  have hSQK : SQTKGroup ↥K := B69.sqtk_subgroup hA21 hY φ hφ hKH h.isQuasisimple
  have hSQG : SQTKGroup ↥G₀ := InternalSec.sqtkGroup_of_two_pow h.K_le h.normal_G₀
    (fun y hy => ⟨1, by simpa using h.sq_mem hy⟩) hSQK
  exact ⟨hSQG, h.quasithinGenFitting_eq.symm, h.isQuasisimple, h.isIrrSec⟩

end Hypotheses

section Dispatch

variable {W : Type} [CommGroup W] [Finite W] {G₀ K S : Subgroup (MulAut W)} {a : MulAut W} {z : W}

theorem one_false (hB45 : AsB45) (cs : OneCases) (hC : Ctx1 W G₀ K a S z) (hB : B4Hyp G₀ K) :
    False := by
  have hq2 : qOf G₀ ≤ ((2 : ℚ) : WithTop ℚ) :=
    qOf_le_two hC.exp hC.a_mem hC.a1 hC.a2 hC.rk
  have hqh : qhatOf G₀ ≤ ((2 : ℚ) : WithTop ℚ) :=
    qhatOf_le_two hC.exp hC.a_mem hC.a1 hC.a2 hC.rk
  have hJ : ∀ J : Subgroup (MulAut W), J ≤ G₀ → CovOrder3 J → False := fun J hJ hcov =>
    hC.false_of_cov hJ hcov
  have hffJ : ffJ G₀ ≤ G₀ := B6.ffJ_le G₀
  have hbig := hC.big
  rcases hB45 W hC.exp G₀ K hB hqh with ⟨-, ⟨A, hA⟩, hall⟩ | ⟨-, htab⟩ | ⟨-, h2q, -⟩
  ·
    rcases hall A hA with ⟨-, ⟨n, hn⟩, -, -⟩ | ⟨-, ⟨n, hn⟩, -⟩ | ⟨⟨n, hn, -⟩, -⟩ |
      ⟨⟨n, hn, -, h1⟩, -⟩ | ⟨⟨n, hn57, π, hπ, -⟩, -⟩ | ⟨-, hn, -⟩ | ⟨-, -, -, hcard, -⟩ |
      ⟨-, -, -, ⟨K', hK', hfin, Γ₀, hc, hdet, hhat, hcen, π, hπ, -⟩⟩ | ⟨-, n, hn45, hn, -⟩ |
      ⟨hext, -⟩ | ⟨hG, hJK, -, -, π, hπ, -⟩
    ·
      exact cs.sl2 W G₀ K S a z hC ⟨n, hn⟩
    ·
      exact hJ K hC.K_le (cs.covSL3 W K n hn)
    ·
      exact hJ _ hffJ (cs.covSp4 W _ n hn)
    ·
      have hn1 : 1 ≤ n := B5.one_le_of_g2Natural hn
      rcases Nat.lt_or_ge n 2 with hlt | hge
      · have : n = 1 := by omega
        subst this
        exact hJ _ hffJ (cs.covG2One W _ hn)
      · have hK : ffJ G₀ = K := h1 (by omega)
        rw [hK] at hn
        exact cs.g2 W G₀ K S a z hC ⟨n, hge, hn⟩
    ·
      have hsym : SymmetricNatural (ffJ G₀) ⊤ ⊥ n := ⟨π, hπ⟩
      rcases hn57 with rfl | rfl
      · have := cs.sizes.sym W _ 5 hsym
        have h16 : 2 ^ (5 - 1) < 2 ^ 6 := by norm_num
        omega
      · exact hJ _ hffJ (cs.covSym7 W _ hsym)
    ·
      have := cs.sizes.alt W K 6 hn
      have h32 : 2 ^ (6 - 1) < 2 ^ 6 := by norm_num
      omega
    ·
      have h16 : 2 ^ 4 < 2 ^ 6 := by norm_num
      omega
    ·
      exact cs.hat W G₀ K S a z hC (Or.inl ⟨K', hK', hfin, Γ₀, hc, hdet, hhat, hcen, ⟨π, hπ⟩⟩)
    ·
      have h := cs.sizes.sl W K n 1 hn
      rcases hn45 with rfl | rfl
      · have h16 : 2 ^ (4 * 1) < 2 ^ 6 := by norm_num
        omega
      · have h32 : 2 ^ (5 * 1) < 2 ^ 6 := by norm_num
        omega
    ·
      exact hJ K hC.K_le (cs.covL42 W K hext)
    ·
      exact cs.extSq5 W G₀ K S a z hC (hG.trans hJK) ⟨π, hπ⟩
  ·
    rcases htab with ⟨hA7, -, -⟩ | ⟨m, hm, hOrth, -, -⟩ | ⟨m, hSU3, -, -⟩ | ⟨f, hSz, -, -⟩ |
      ⟨m, -, -, h2q, -⟩ | ⟨hG2, -, -⟩ | ⟨-, h2q⟩ | ⟨hhat, -⟩ | ⟨-, h2q⟩ | ⟨hcode, -⟩ | ⟨-, h2q⟩
    · exact hJ K hC.K_le (cs.covAlt7 W K hA7)
    · exact cs.orth4 W G₀ K S a z hC ⟨m, hm, hOrth⟩
    · exact cs.su3 W G₀ K S a z hC ⟨m, hSU3⟩
    · exact cs.sz W G₀ K S a z hC ⟨f, hSz⟩
    · exact absurd hq2 (not_le.2 h2q)
    · exact hJ K hC.K_le (cs.covG2Der W K hG2)
    · exact absurd hq2 (not_le.2 h2q)
    · exact cs.hat W G₀ K S a z hC (Or.inr hhat)
    · exact absurd hq2 (not_le.2 h2q)
    · exact cs.m22code W G₀ K S a z hC hcode
    · exact absurd hq2 (not_le.2 h2q)
  · exact absurd hq2 (not_le.2 h2q)

theorem one_component_false (hA21 : AsA21SQTKSection) (hB45 : AsB45) (cs : OneCases)
    {H : Subgroup (MulAut W)} (hq : G64.IsQuotientOfSQTKCat ↥H) (hKH : K ≤ H)
    (hC : Ctx1 W G₀ K a S z) : False :=
  one_false hB45 cs hC (b4Hyp_of_ctx1 hA21 hq hKH hC)

end Dispatch

end S153G93D

end CFSG.Quasithin
