module

public import CFSG.Quasithin.H13.A5W1622q
public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Quasithin.H13.A5S136m
public import CFSG.Quasithin.H13.A5Y1367c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

theorem exists_kbar_plus (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    {K : Subgroup G} (hKG : K ≤ Subgroup.centralizer ({S.v12} : Set G))
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G)) (hLv : S.Lv ≤ Subgroup.normalizer (K : Set G)) :
    ∃ π : ↥K ⧸ CFSG.pCore 2 ↥K →* ↥(S.plus K), Function.Surjective π := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := S.isTwoReducedIn_WK h1222 h517 hF hKG hT
  have hKH : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer (S.WK K : Set G) := hKH.trans hR.2.1
  set φ := InternalSec.autOnHom hKW with hφ
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hKW
  have hHK : S.HK K ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer hLv) hT
  have hOC : pCoreOf 2 K ≤ Subgroup.centralizer (S.WK K : Set G) := by
    refine hR.2.2.2 _ ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
      (fun g hg => C1.mem_normalizer_blockQ (hHK hg)) fun d hd => ?_
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have h1 : d ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    rw [h1]
    exact Subgroup.one_mem _
  have hker : CFSG.pCore 2 ↥K ≤ φ.ker := by
    intro q hq
    rw [InternalSec.mem_ker_autOnHom]
    have hq' : q ∈ CFSG.Open.pCore 2 ↥K := by exact hq
    exact hOC ⟨q, hq', rfl⟩
  refine ⟨QuotientGroup.lift (CFSG.pCore 2 ↥K) φ hker, ?_⟩
  intro y
  obtain ⟨k, rfl⟩ := hφs y
  exact ⟨QuotientGroup.mk k, rfl⟩

theorem card_of_sl2_quotient {X P : Type} [Group X] [Group P] (hP : CFSG.IsQuasisimple P)
    (π : X →* P) (hπ : Function.Surjective π) {F : Subgroup X} [hFn : F.Normal]
    (hF : Group.IsSolvable ↥F) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) (hψ : Function.Surjective ψ)
    (hψk : ψ.ker = F) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ 2 ∧ Nat.card (P ⧸ Subgroup.center P) * c = p * (p ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : (F.map π).Normal := Subgroup.Normal.map hFn π hπ
  have hFs : Group.IsSolvable ↥(F.map π) :=
    Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π F)
  have hFc : F.map π ≤ Subgroup.center P := le_center_of_isSolvable_of_isQuasisimple hP hFs
  let σ : X →* P ⧸ Subgroup.center P := (QuotientGroup.mk' (Subgroup.center P)).comp π
  have hσ : Function.Surjective σ := (QuotientGroup.mk'_surjective _).comp hπ
  have hFσ : ψ.ker ≤ σ.ker := by
    rw [hψk]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hFc ⟨x, hx, rfl⟩
  let θ := ψ.liftOfSurjective hψ ⟨σ, hFσ⟩
  have hθ : Function.Surjective θ := by
    intro y
    obtain ⟨x, rfl⟩ := hσ y
    exact ⟨ψ x, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x⟩
  have : Nontrivial (P ⧸ Subgroup.center P) := by
    obtain ⟨a, b, hab⟩ := hP.2.2
    exact ⟨⟨a * b, b * a, hab⟩⟩
  obtain ⟨h1, h2⟩ := card_mul_card_ker_of_sl2 hp hp5 θ hθ
  exact ⟨Nat.card θ.ker, Nat.card_pos, h2, h1⟩

theorem kbar_cases (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) (h36 : A36ForSQTK)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) (hYz : S.InYz K)
    (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    (hN : Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 168 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 360 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 2520 ∨
      Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 6048) :
    CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∨
      (Nat.card (↥(S.plus K) ⧸ Subgroup.center ↥(S.plus K)) = 168 ∧
        A36Case3 ↥(modO2Image (Subgroup.centralizer ({S.v12} : Set G)) K)) := by
  have hLv := S.Lv_le_normalizer_of_mem_cComp h1222 h517 h37 h38 hK
  obtain ⟨π, hπ⟩ := S.exists_kbar_plus h1222 h517 hF hYz.1 hT hLv
  have hq := S.isQuasisimple_plus h1222 h517 hF hYz hT
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  obtain ⟨ψ, hψs, hψk⟩ := exists_modO2_surjection hK
  let eX : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(modO2Image Gv K) :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  let πX : ↥(modO2Image Gv K) →* ↥(S.plus K) := π.comp eX.symm.toMonoidHom
  have hπX : Function.Surjective πX := hπ.comp eX.symm.surjective
  have hA := lemma_1_2_1_four S.h13.qtke S.h13.simple S.h13.nonabelian h36
    (S.pCoreOf_Gv_ne_bot h1222 h517 hF) hK
  rcases hA with ⟨hcomp, -, -⟩ | ⟨hcomp, -, -⟩ | h3 | h4
  · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hcomp.1)
  · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv eX.symm hcomp.1)
  · right
    have h3' := h3
    obtain ⟨p, hp, hp3, -, ⟨eF⟩, hnat⟩ := h3
    obtain ⟨-, ψ₃, hψ₃s, hψ₃k, -⟩ := hnat
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := by
      have : IsMulCommutative (Multiplicative (Fin 2 → ZMod p)) := inferInstance
      exact Group.isSolvable_of_surjective (f := eF.symm.toMonoidHom) eF.symm.surjective
    have hp5 : 5 ≤ p := by
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
      omega
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs hp hp5 ψ₃ hψ₃s hψ₃k
    exact ⟨(prime_eq_seven_of_sl2 hp hp3 hc1 hc2 hN hcard).1, h3'⟩
  · exfalso
    obtain ⟨-, hnil, ⟨e5⟩, -⟩ := h4
    have hFs : Group.IsSolvable ↥(CFSG.fittingSubgroup ↥(modO2Image Gv K)) := inferInstance
    let ψ₄ := e5.toMonoidHom.comp (QuotientGroup.mk' (CFSG.fittingSubgroup ↥(modO2Image Gv K)))
    have hψ₄ : Function.Surjective ψ₄ := e5.surjective.comp (QuotientGroup.mk'_surjective _)
    have hψ₄k : ψ₄.ker = CFSG.fittingSubgroup ↥(modO2Image Gv K) := by
      ext x
      simp [ψ₄]
    obtain ⟨c, hc1, hc2, hcard⟩ := card_of_sl2_quotient hq πX hπX hFs Nat.prime_five le_rfl ψ₄
      hψ₄ hψ₄k
    rcases hN with h | h | h | h <;> rw [h] at hcard <;> omega

end Setting

end CFSG.Quasithin.H13.A5
