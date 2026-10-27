module

public import CFSG.Quasithin.Background.RonanE52Two
public import CFSG.Quasithin.Background.RonanE52Second
public import CFSG.Quasithin.Background.RonanE52One

public section

namespace CFSG.Quasithin.RonanE52

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_mem_E {P : Subgroup G} {i j : ℕ} (hP : IsSylowIn 2 P ⊤) {A K : Subgroup G}
    (hA : IsElemAbelianCorank P i A)
    (hK : E1.IsE j ⊤ P A K) {𝒢 : Subgroup G} (hPG : P ≤ 𝒢)
    (hcent : ∀ D₁ : Subgroup G, D₁ ≤ omegaOneCenterOf (H13.thompsonJk (i + j) P) →
      Nat.card ↥(omegaOneCenterOf (H13.thompsonJk (i + j) P)) ≤ 2 ^ (i + j) * Nat.card ↥D₁ →
      Subgroup.centralizer (D₁ : Set G) ≤ 𝒢) :
    K ≤ 𝒢 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hAcard⟩ := E3.card_le_of_isE hP hA.1 hA.2.1 hK
  set Q := pCoreOf 2 K with hQdef
  have hQK : Q ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hQP : Q ≤ P := RonanE51.pCoreOf_le_of_isSylow hK.2.2.1
  set n := i + j with hn
  set J := H13.thompsonJk n P with hJdef
  set D := omegaOneCenterOf J with hDdef
  set W := E5.wGen n P Q with hWdef
  have hA₁ : A ⊓ Q ∈ E5.wFam n P Q := RonanE51.inf_mem_wFam hA hAcard
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := E5.le_normalizer_wGen n hKQ
  have hWQ : W ≤ Q := E5.wGen_le n P Q
  have hWJ : W ≤ J := E5.wGen_le_thompsonJk hQP
  have hAJ : A ≤ J := RonanE51.le_thompsonJk_of_corank (Nat.le_add_right i j) hA
  have hDK : D ≤ K := RonanE51.omegaOneCenter_le_of_tau hAJ hK.2.1
  have hDP : D ≤ P := (omegaOneCenterOf_le J).trans (E5.thompsonJk_le n P)
  have hDW : D ≤ Subgroup.centralizer (W : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun w hw => mem_centralizer_of_mem_omegaOneCenterOf hd (hWJ hw)
  have hDel : IsElemAbelian 2 D := B2F.isElemAbelian_omegaOneCenterOf _
  have hD2 : IsPGroup 2 D := B2F.isPGroup_of_isElemAbelian hDel
  have hDA : ∀ d ∈ D, ∀ a ∈ A, d * a = a * d := fun d hd a ha =>
    (mem_centralizer_of_mem_omegaOneCenterOf hd (hAJ ha)).symm
  have hDQW : D ⊓ Q ≤ W :=
    RonanE51.le_wGen_of_commute hA₁ (B2F.isElemAbelian_mono inf_le_left hDel) inf_le_right
      fun v hv a ha => hDA v hv.1 a ha.1
  have hQD : Q ≤ Subgroup.normalizer (D : Set G) :=
    (hQP.trans (E5.le_normalizer_thompsonJk n P)).trans
      (normalizer_le_normalizer_omegaOneCenterOf _)
  obtain ⟨hDS, hKS, hres⟩ := RonanE51.stabilizer_facts hKQ hKW hWQ hQ2 hDK hDW hQD hDQW
  set S := K ⊓ Subgroup.centralizer (W : Set G) ⊓ E5.quotStab Q W with hSdef
  have hSK : S ≤ K := inf_le_left.trans inf_le_left
  have hDQidx : Nat.card D ≤ 2 ^ n * Nat.card ↥(D ⊓ Q) :=
    RonanE51.card_le_two_pow_mul_card_inf hA hAcard hDel hDP hDA
  have hCQ : Subgroup.centralizer (Q : Set G) ≤ 𝒢 :=
    (Subgroup.centralizer_le (fun x hx => hx.2 : ((D ⊓ Q : Subgroup G) : Set G) ⊆ (Q : Set G))).trans
      (hcent (D ⊓ Q) inf_le_left hDQidx)
  have hAG : A ≤ 𝒢 := hA.1.trans hPG
  have hres2 : twoResidual K ≤ 𝒢 := by
    have hXn : (S.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hSK).2 hKS
    have hD2' : IsPGroup 2 (D.subgroupOf K) :=
      hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hDK).symm
    have hXK' : twoResidual (S.subgroupOf K) ≤
        Subgroup.centralizer (CFSG.Open.pCore 2 ↥K : Set ↥K) := by
      intro y hy
      have hy' : (y : G) ∈ twoResidual S := by
        have h1 : (twoResidual (S.subgroupOf K)).map K.subtype = twoResidual S := by
          rw [E1.map_twoResidual, Subgroup.map_subgroupOf_eq_of_le hSK]
        rw [← h1]
        exact Subgroup.mem_map_of_mem _ hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzQ : (z : G) ∈ Q := Subgroup.mem_map_of_mem K.subtype hz
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hres hy') _ hzQ)
    rcases hK.2.2.2 with ⟨hE, -⟩ | ⟨hE, -⟩
    ·
      obtain ⟨p, hp, hp2, h22, -, hPA, -⟩ := hE
      have hQU : CFSG.pCore 2 ↥K ≤ 𝒢.comap K.subtype := fun y hy =>
        hPG (hQP (Subgroup.mem_map_of_mem K.subtype hy))
      have hSU : twoResidual (S.subgroupOf K) ≤ 𝒢.comap K.subtype := fun y hy => by
        have hy' : (y : G) ∈ twoResidual S := by
          have h1 : (twoResidual (S.subgroupOf K)).map K.subtype = twoResidual S := by
            rw [E1.map_twoResidual, Subgroup.map_subgroupOf_eq_of_le hSK]
          rw [← h1]
          exact Subgroup.mem_map_of_mem _ hy
        exact hCQ (hres hy')
      have hcov : ∀ c : ↥K, QuotientGroup.mk' (CFSG.pCore 2 ↥K) c ∈
          CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) →
          QuotientGroup.mk' (CFSG.pCore 2 ↥K) c ∈ Subgroup.centralizer
            (((D.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :
              Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) : Set (↥K ⧸ CFSG.pCore 2 ↥K)) →
          ∀ a ∈ A.subgroupOf K, ⁅c, a⁆ ∈ 𝒢.comap K.subtype := by
        intro c _ hcC a ha
        have hcK : (c : G) ∈ K := c.2
        have hcQ : ∀ d ∈ D, (c : G) * d * (c : G)⁻¹ * d⁻¹ ∈ Q := by
          intro d hd
          have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨d, hDK hd⟩ : ↥K) ∈
              (D.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) :=
            Subgroup.mem_map_of_mem _ (show (⟨d, hDK hd⟩ : ↥K) ∈ D.subgroupOf K from hd)
          have h2 := Subgroup.mem_centralizer_iff.1 hcC _ h1
          have h3 : c * (⟨d, hDK hd⟩ : ↥K) * c⁻¹ * (⟨d, hDK hd⟩ : ↥K)⁻¹ ∈
              CFSG.pCore 2 ↥K := by
            rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥K), MonoidHom.mem_ker]
            simp only [map_mul, map_inv]
            rw [← h2]
            group
          exact ⟨_, h3, rfl⟩
        have hcnorm : (c : G) ∈ Subgroup.normalizer ((D ⊔ Q : Subgroup G) : Set G) := by
          refine E1.mem_normalizer_of_conj_mem fun x hx => ?_
          rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right D Q
            (hDK.trans hKQ)] at hx
          obtain ⟨d, hd, q, hq, rfl⟩ := hx
          have hcq : (c : G) * q * (c : G)⁻¹ ∈ Q :=
            (Subgroup.mem_normalizer_iff.1 (hKQ hcK) q).1 hq
          have e : (c : G) * (d * q) * (c : G)⁻¹ =
              ((c : G) * d * (c : G)⁻¹ * d⁻¹) * d * ((c : G) * q * (c : G)⁻¹) := by group
          rw [e]
          exact (D ⊔ Q).mul_mem ((D ⊔ Q).mul_mem (Subgroup.mem_sup_right (hcQ d hd))
            (Subgroup.mem_sup_left hd)) (Subgroup.mem_sup_right hcq)
        have hAQ' : Nat.card A ≤ 2 ^ j * Nat.card ↥(A ⊓ (D ⊔ Q)) :=
          hAcard.trans (Nat.mul_le_mul_left _
            (Subgroup.card_le_of_le (inf_le_inf_left A le_sup_right)))
        obtain ⟨D₁, hD₁, hD₁c, hAk⟩ :=
          exists_cjSub_le_centralizer hA (sup_le hDP hQP) hAQ' le_sup_left hcnorm
        have hAc : cjSub (c : G) A ≤ 𝒢 := hAk.trans (hcent D₁ hD₁ hD₁c)
        have haA : (a : G) ∈ A := ha
        show ((⁅c, a⁆ : ↥K) : G) ∈ 𝒢
        have e : ((⁅c, a⁆ : ↥K) : G) = ((c : G) * a * (c : G)⁻¹) * (a : G)⁻¹ := rfl
        rw [e]
        exact 𝒢.mul_mem (hAc (mem_cjSub.2 (by simpa [mul_assoc] using haA)))
          (𝒢.inv_mem (hAG haA))
      have hcover := comap_pCore_le_of_cover (A' := A.subgroupOf K) (D' := D.subgroupOf K)
        (S' := S.subgroupOf K) (U := 𝒢.comap K.subtype) hp hp2 hPA (hSn := hXn) hD2'
        (Subgroup.subgroupOf_mono K hDS) (fun d hd a ha => Subtype.ext (hDA d hd a ha)) hQU hSU
        hcov
      have h2 : twoResidual (⊤ : Subgroup ↥K) ≤ E1.oTwoP ↥K p := by
        refine twoResidual_le_of_isTwoQuotient le_top
          (top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr inferInstance)) ?_
        intro y _
        exact E1.exists_pow_mem_of_mem_pCore (M := E1.oTwoP ↥K p) (fun q => by
          have hq : q ∈ E1.oTwoPTwo ↥K p := by rw [h22]; exact Subgroup.mem_top q
          exact hq) y
      rw [E1.twoResidual_eq_map_top K]
      rintro _ ⟨y, hy, rfl⟩
      exact hcover (h2 hy)
    ·
      rcases dichotomy_two hE hD2' (hXn := hXn) (Subgroup.subgroupOf_mono K hDS) hXK' with h | h
      ·
        refine le_trans ?_ hCQ
        rw [E1.twoResidual_eq_map_top K]
        rintro _ ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨z, hz, rfl⟩
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 (h hy) z hz)
      ·
        have hDQ : D ≤ Q := by
          intro d hd
          have := h (show (⟨d, hDK hd⟩ : ↥K) ∈ D.subgroupOf K from hd)
          exact ⟨_, this, rfl⟩
        have hgen : ∀ k ∈ K, cjSub k A ≤ 𝒢 := by
          intro k hk
          obtain ⟨D₁, hD₁, hD₁c, hAk⟩ :=
            exists_cjSub_le_centralizer hA hQP hAcard hDQ (hKQ hk)
          exact hAk.trans (hcent D₁ hD₁ hD₁c)
        calc twoResidual K ≤ conjClosure A K := E1.twoResidual_le_conjClosure ⟨j, hK⟩
          _ ≤ 𝒢 := conjClosure_le fun k hk a ha =>
              hgen k hk (by rw [mem_cjSub]; simpa [mul_assoc] using ha)
  calc K = (P ⊓ K) ⊔ twoResidual K := (sup_twoResidual_eq hK.2.2.1).symm
    _ ≤ 𝒢 := sup_le (inf_le_left.trans hPG) hres2

end CFSG.Quasithin.RonanE52
