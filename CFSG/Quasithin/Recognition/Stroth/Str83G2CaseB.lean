module

public import CFSG.Quasithin.Recognition.Stroth.Str83G2CaseII2
public import CFSG.Quasithin.Recognition.Stroth.L2ChiefNatural
public import CFSG.Quasithin.Vol2.Ch3g316Red
public import CFSG.RankThree.GF2n.Tim81.Sec2.SL2Small

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.B2F
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.RankThree.GF2n.Tim81.Sec2
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]
variable {L1 L2 S : Subgroup G} {a : ℕ}

private theorem not_ffInt_z1_of_caseII
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hV : IsElemAbelian 2 (Z1 L1 L2 S)) :
    ¬ IsFFInt (L1 ⊔ S) (Z1 L1 L2 S) hV ∧
      ¬ IsDualFFInt (L1 ⊔ S) (Z1 L1 L2 S) hV := by
  have hB1 : VSzBig L1 ∨ VU3Big L1 := Or.inl ⟨a, ha, hSz⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    rw [hsup1]
    refine sup_le ?_ ?_
    · exact ((le_sup_left : L1 ≤ P1 L1 L2 S).trans
        ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))))
    · exact (Q1_le_centralizer_Z1 L1 L2 S).trans
        (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))
  have hSyl1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hC : S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = Q1 L1 L2 S :=
    inf_centralizer_z1_eq_q1_of_caseII hF hB hB1 hII
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hq : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdisp : ∀ t ∈ S, t * t ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
      t ∉ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
      (2 ^ (2 * a + 1)) ^ 2 ≤
        (Z1 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) := by
    intro t htS ht2 htC
    have htQ1 : t ∉ Q1 L1 L2 S := fun htQ =>
      htC (Q1_le_centralizer_Z1 L1 L2 S htQ)
    have htH : t ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) htS
    have ht2Q1 : t * t ∈ Q1 L1 L2 S := by
      have htSC : t * t ∈ S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        ⟨S.mul_mem htS htS, ht2⟩
      rwa [hC] at htSC
    have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
      rw [hsup1]
      exact pCoreOf_sup_pCoreOf hF.1
    have hHc : ¬ L1 ⊔ S ≤
        ((L1 ⊔ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) ⊔ pCoreOf 2 (L1 ⊔ S) := by
      rw [hpCore1]
      intro hle
      have hQ1C : Q1 L1 L2 S ≤
          (L1 ⊔ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        le_inf (hQ1S.trans le_sup_right) (Q1_le_centralizer_Z1 L1 L2 S)
      have hHleC : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        (hle.trans (sup_le le_rfl hQ1C)).trans inf_le_right
      exact hII (by rwa [hsup1] at hHleC)
    obtain ⟨eSz⟩ := hSz
    have hX : (∃ b : ℕ, 1 ≤ b ∧ 2 ^ (2 * a + 1) = 2 ^ (2 * b + 1) ∧
        Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* CFSG.Open.Sz b)) ∨
        (∃ n : ℕ, 2 ≤ n ∧ 2 ^ (2 * a + 1) = 2 ^ n ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
            (Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* CFSG.Open.StatedSU 3 (2 ^ n) F) ∨
              Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃*
                CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)))) := by
      refine Or.inl ⟨a, ha, rfl, ?_⟩
      rw [hsup1]
      exact ⟨(oTwoQuotSupEquiv hF.1).trans eSz⟩
    exact sq_le_relIndex_centralizer_of_sq_mem hX
      (fun v hv => by rw [← pow_two]; exact hV.2 v hv) hHZ1 hHc htH
      (by rwa [hpCore1]) (by rwa [hpCore1])
  have hhab : ∀ A : Subgroup G, A ≤ S →
      (∀ x ∈ A, ∀ y ∈ A,
        x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G) ∧
          x * x ∈ Subgroup.centralizer (Z1 L1 L2 S : Set G)) →
      (A ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)).relIndex A ≤ 2 ^ (2 * a + 1) := by
    intro A hAS hA
    have hsq : ∀ x ∈ A, x ^ 2 ∈ Q1 L1 L2 S := by
      intro x hx
      rw [pow_two]
      have hxSC : x * x ∈ S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
        ⟨S.mul_mem (hAS hx) (hAS hx), (hA x hx x hx).2⟩
      rwa [hC] at hxSC
    have hqU : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ (2 * a + 1)) :=
      Or.inl ⟨a, ha, rfl, hSz⟩
    have h := relIndex_inf_q1_le hF.1 hS1 hqU hAS hsq
    have hAinf : A ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) = A ⊓ Q1 L1 L2 S := by
      calc A ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)
          = (A ⊓ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
            rw [inf_eq_left.mpr hAS]
        _ = A ⊓ (S ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) := by rw [inf_assoc]
        _ = A ⊓ Q1 L1 L2 S := by rw [hC]
    rwa [hAinf]
  exact not_isFFInt_of_disp hV hHZ1 hSyl1 hq hdisp hhab

private theorem relIndex_centralizer_cjSub {G : Type} [Group G] (g : G) (X U : Subgroup G) :
    (Subgroup.centralizer (cjSub g X : Set G)).relIndex (cjSub g U) =
      (Subgroup.centralizer (X : Set G)).relIndex U := by
  rw [← cjSub_centralizer]
  exact Subgroup.relIndex_map_map_of_injective
    (f := (MulAut.conj g).toMonoidHom) (Subgroup.centralizer (X : Set G)) U
    (MulAut.conj g).injective

private theorem sup_eq_of_normal_not_le_pCoreOf {H K : Subgroup G}
    (hsim : IsSimpleGroup (oTwoQuot ↥H)) (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hnot : ¬ K ≤ pCoreOf 2 H) :
    K ⊔ pCoreOf 2 H = H := by
  classical
  let π : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H)
  let Kq : Subgroup (oTwoQuot ↥H) := (K.subgroupOf H).map π
  have hKnorm : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hKqN : Kq.Normal :=
    Subgroup.Normal.map hKnorm π (QuotientGroup.mk'_surjective _)
  have hKqne : Kq ≠ ⊥ := by
    intro hbot
    apply hnot
    intro x hx
    have hxH : x ∈ H := hKH hx
    have hxmem : π ⟨x, hxH⟩ ∈ Kq :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
    rw [hbot] at hxmem
    have hx1 : π ⟨x, hxH⟩ = 1 := Subgroup.mem_bot.mp hxmem
    have hxR : (⟨x, hxH⟩ : ↥H) ∈ pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp hx1
    exact (CFSG.mem_openPCoreOf_iff (⟨x, hxH⟩ : ↥H)).mpr hxR
  have htop : Kq = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal Kq).resolve_left hKqne
  refine le_antisymm (sup_le hKH (pCoreOf_le 2 H)) ?_
  intro h hh
  have hmem : π ⟨h, hh⟩ ∈ Kq := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkπ⟩ := Subgroup.mem_map.mp hmem
  have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
  have hker : (⟨(k : G)⁻¹ * h, H.mul_mem (H.inv_mem k.2) hh⟩ : ↥H) ∈ pCore 2 ↥H := by
    rw [← QuotientGroup.eq_one_iff]
    change π (k⁻¹ * ⟨h, hh⟩) = 1
    rw [map_mul, map_inv, hkπ, inv_mul_cancel]
  have hq : (k : G)⁻¹ * h ∈ pCoreOf 2 H :=
    (CFSG.mem_openPCoreOf_iff _).mpr hker
  rw [F1.mem_sup_iff_exists_mul_of_normalizes
    (H := K) (K := pCoreOf 2 H) ((pCoreOf_le 2 H).trans hKn)]
  exact ⟨(k : G), hkK, (k : G)⁻¹ * h, hq, by group⟩

theorem str83_partTwo_caseB_steps123
    (hF : F112HypW L1 L2 S) (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (ha : 1 ≤ a) (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    (hII : ¬ L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G))
    (hZ2 : L2 ⊔ S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hJ : ¬ jAtLeast (2 ^ pRank 2 S) (2 ^ (2 * a + 1)) S ≤ Q1 L1 L2 S)
    (hBc : Z1 L1 L2 S ≤ Q2 L1 L2 S) :
    IsElemAbelian 2 (conjClosure (Z1 L1 L2 S) (L2 ⊔ S)) ∧
      conjClosure (Z1 L1 L2 S) (L2 ⊔ S) ≤ Q1 L1 L2 S ⊓ Q2 L1 L2 S ∧
      (∀ c : ℕ, IsChiefSeriesFrom (L2 ⊔ S)
        (conjClosure (Z1 L1 L2 S) (L2 ⊔ S))
        (conjClosure (Z1 L1 L2 S) (L2 ⊔ S)) c → c = 2) ∧
      ∀ (L N : Subgroup G) (hstep : IsChiefStep (L2 ⊔ S)
          (conjClosure (Z1 L1 L2 S) (L2 ⊔ S)) L N)
        (hUH : conjClosure (Z1 L1 L2 S) (L2 ⊔ S) ≤ L2 ⊔ S),
        ¬ IsCentralStep (L2 ⊔ S) L N →
        ∀ hE : IsElemAbelian 2 (Ch3z.chiefMod L N),
          IsNaturalChiefStep (L2 ⊔ S) (conjClosure (Z1 L1 L2 S) (L2 ⊔ S)) L N hstep hUH hE
            (2 * a + 1) := by
  have hB1 : VSzBig L1 ∨ VU3Big L1 := Or.inl ⟨a, ha, hSz⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (hB1.imp_right Or.inl)
  have hS2 : S = (S ⊓ L2) ⊔ Q2 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_right hF.1 hB
      (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩))
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S := sup_eq_of_S_eq hS1
  have hsup2 : L2 ⊔ S = L2 ⊔ Q2 L1 L2 S := sup_eq_of_S_eq_right hS2
  have hpCore1 : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hpCore2 : pCoreOf 2 (L2 ⊔ S) = Q2 L1 L2 S := by
    rw [hsup2]
    have h := pCoreOf_sup_pCoreOf (L1 := L2) (L2 := L1) (S := S) hF.1.symm
    simpa [Q1, Q2, P1, P2, bigB_comm] using h
  have hD11 : D11Hyp (L1 ⊔ S) (L2 ⊔ S) S (Z1 L1 L2 S) (borelOf L2 S ⊔ S) :=
    d11Hyp_of_caseII hF hB hB1 hL2 (by omega) hII
  have hV : IsElemAbelian 2 (Z1 L1 L2 S) := hD11.reduced.2.2.1
  have hVR₂ : Z1 L1 L2 S ≤ pCoreOf 2 (L2 ⊔ S) := by
    rw [hpCore2]
    exact hBc
  set H : Subgroup G := L2 ⊔ S with hHdef
  set V : Subgroup G := Z1 L1 L2 S with hVdef
  set X : Subgroup G := conjClosure V H with hXdef
  have hXe : IsElemAbelian 2 X := by
    have hff := (not_ffInt_z1_of_caseII hF hB ha hSz hL2 hII hV).1
    exact D15Proof.isElemAbelian_conjClosure hD11 hff hVR₂
  have hQ1S : Q1 L1 L2 S ≤ S := by
    conv_rhs => rw [hS1]
    exact le_sup_right
  have hQ2S : Q2 L1 L2 S ≤ S := by
    conv_rhs => rw [hS2]
    exact le_sup_right
  have hSH : S ≤ H := by rw [hHdef]; exact le_sup_right
  have hHZ1 : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    rw [hsup1]
    refine sup_le ?_ ?_
    · exact ((le_sup_left : L1 ≤ P1 L1 L2 S).trans
        ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
          (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S))))
    · exact (Q1_le_centralizer_Z1 L1 L2 S).trans
        (Subgroup.centralizer_le_normalizer (Z1 L1 L2 S : Set G))
  have hHc : ¬ L1 ⊔ S ≤
      ((L1 ⊔ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G)) ⊔ pCoreOf 2 (L1 ⊔ S) := by
    rw [hpCore1]
    intro hle
    have hQ1C : Q1 L1 L2 S ≤
        (L1 ⊔ S) ⊓ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
      le_inf (hQ1S.trans le_sup_right) (Q1_le_centralizer_Z1 L1 L2 S)
    have hHleC : L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) :=
      (hle.trans (sup_le le_rfl hQ1C)).trans inf_le_right
    exact hII (by rwa [hsup1] at hHleC)
  have hSyl1 : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq1 : 1 < 2 ^ (2 * a + 1) := lt_of_lt_of_le (by norm_num) hq2
  have hXsz : (∃ b : ℕ, 1 ≤ b ∧ 2 ^ (2 * a + 1) = 2 ^ (2 * b + 1) ∧
      Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* CFSG.Open.Sz b)) ∨
      (∃ n : ℕ, 2 ≤ n ∧ 2 ^ (2 * a + 1) = 2 ^ n ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
          (Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃* CFSG.Open.StatedSU 3 (2 ^ n) F) ∨
            Nonempty (oTwoQuot ↥(L1 ⊔ S) ≃*
              CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (2 ^ n) F)))) := by
    obtain ⟨eSz⟩ := hSz
    refine Or.inl ⟨a, ha, rfl, ?_⟩
    rw [hsup1]
    exact ⟨(oTwoQuotSupEquiv hF.1).trans eSz⟩
  have hM7 : ∀ t ∈ S, t * t ∈ Q1 L1 L2 S → t ∉ Q1 L1 L2 S →
      (2 ^ (2 * a + 1)) ^ 2 ≤
        (Z1 L1 L2 S ⊓ Subgroup.centralizer ({t} : Set G)).relIndex (Z1 L1 L2 S) := by
    intro t htS ht2 htQ1
    have htH : t ∈ L1 ⊔ S := (le_sup_right : S ≤ L1 ⊔ S) htS
    exact sq_le_relIndex_centralizer_of_sq_mem hXsz
      (fun v hv => by rw [← pow_two]; exact hV.2 v hv) hHZ1 hHc htH
      (by rwa [hpCore1]) (by rwa [hpCore1])
  have hM5 : ∀ E : Subgroup G, E ≤ S → (∀ x ∈ E, x * x = 1) →
      (E ⊓ Q1 L1 L2 S).relIndex E ≤ 2 ^ (2 * a + 1) := by
    intro E hES hE
    have hqU : IsSzU3Quot (oTwoQuot ↥L1) (2 ^ (2 * a + 1)) :=
      Or.inl ⟨a, ha, rfl, hSz⟩
    exact relIndex_inf_q1_le hF.1 hS1 hqU hES
      (fun x hx => by rw [pow_two, hE x hx]; exact (Q1 L1 L2 S).one_mem)
  have hHleP2 : H ≤ P2 L1 L2 S := by
    rw [hHdef, hHdef.symm.trans hsup2]
    exact sup_le le_sup_left (pCoreOf_le 2 (P2 L1 L2 S))
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef]
    exact le_normalizer_conjClosure V H
  have hXQ2 : X ≤ Q2 L1 L2 S := by
    rw [hXdef]
    refine conjClosure_le fun g hg v hv => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 (P2 L1 L2 S) (hHleP2 hg)) v).mp
      (by
        have h : v ∈ Q2 L1 L2 S := hpCore2 ▸ hVR₂ hv
        simpa [Q2] using h)
  have hXQ1 : X ≤ Q1 L1 L2 S := by
    rw [hXdef]
    refine conjClosure_le fun g hg v hv => ?_
    set w : G := g * v * g⁻¹ with hwdef
    have hwX : w ∈ X := by
      rw [hXdef]
      exact mem_conjClosure hg hv
    have hwQ2 : w ∈ Q2 L1 L2 S := hXQ2 hwX
    have hwS : w ∈ S := hQ2S hwQ2
    have hwe : w * w = 1 := by rw [← pow_two]; exact hXe.2 w hwX
    by_contra hwQ1
    have hdisp := hM7 w hwS (by rw [hwe]; exact (Q1 L1 L2 S).one_mem) hwQ1
    have hCV : Z1 L1 L2 S ≤ Subgroup.centralizer ({w} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (congrArg Subtype.val (hXe.1.is_comm.comm
        ⟨z, by rw [hXdef]; exact le_conjClosure V H hz⟩ ⟨w, hwX⟩)).symm
    have hrel1 : (Z1 L1 L2 S ⊓ Subgroup.centralizer ({w} : Set G)).relIndex
        (Z1 L1 L2 S) = 1 := by
      have h : Z1 L1 L2 S ⊓ Subgroup.centralizer ({w} : Set G) = Z1 L1 L2 S :=
        inf_eq_left.mpr hCV
      rw [h, Subgroup.relIndex_self]
    rw [hrel1] at hdisp
    have hq4 : 4 ≤ (2 ^ (2 * a + 1)) ^ 2 := by nlinarith
    omega
  have hXH : X ≤ H := by
    rw [hHdef]
    exact hXQ1.trans (hQ1S.trans le_sup_right)
  have hX2 : IsPGroup 2 X := hXe.isPGroup
  have hXpc : X ≤ pCoreOf 2 H := by
    rw [hpCore2]
    exact hXQ2
  have hXNormalIn : IsNormalIn H X X :=
    ⟨le_rfl, fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (hHX hg) x).mp hx⟩
  have hL2H : IsL2Quot (2 * a + 1) (oTwoQuot ↥H) := by
    obtain ⟨eL⟩ := hL2
    rw [hHdef, hHdef.symm.trans hsup2]
    have hsupQ : L2 ⊔ Q2 L1 L2 S = L2 ⊔ Q1 L2 L1 S := by
      simp [Q1, Q2, P1, P2, bigB_comm]
    rw [hsupQ]
    exact ⟨(oTwoQuotSupEquiv hF.1.symm).trans eL⟩
  have hHsimple : IsSimpleGroup (oTwoQuot ↥H) := by
    rw [hHdef]
    exact isSimpleGroup_oTwoQuot_sup_right_of_isL2Quot hF.1 hS2 (by omega) hL2
  have hCX : H ⊓ Subgroup.centralizer (X : Set G) ≤ Q2 L1 L2 S := by
    by_contra hnot
    set K : Subgroup G := H ⊓ Subgroup.centralizer (X : Set G) with hKdef
    have hKH : K ≤ H := inf_le_left
    have hKnormal : H ≤ Subgroup.normalizer (K : Set G) := by
      intro h hh
      exact A4.mem_normalizer_inf (Subgroup.le_normalizer hh)
        ((hHX.trans (F7.normalizer_le_normalizer_centralizer X)) hh)
    have hKnQ : ¬ K ≤ pCoreOf 2 H := by rw [hpCore2]; exact hnot
    have hKQ2 : K ⊔ pCoreOf 2 H = H :=
      sup_eq_of_normal_not_le_pCoreOf (H := H) (K := K) hHsimple hKH hKnormal hKnQ
    have hHK : H ≤ K ⊔ Q2 L1 L2 S := by
      rw [← hpCore2]
      exact le_of_eq hKQ2.symm
    have hO2K : oTwoUpper H ≤ K :=
      CFSG.Quasithin.Vol2.Ch11.SecD.oTwoUpper_le_of_le_sup'
        (X := H) (Y := K) (T := Q2 L1 L2 S) hHK
        (pCoreOf_isPGroup 2 (P2 L1 L2 S)) (fun q hq => hKnormal (hSH (hQ2S hq)))
    have hcomm : ⁅X, oTwoUpper H⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hO2K.trans inf_le_right
    obtain ⟨c, hser⟩ := D15Proof.exists_isChiefSeriesFrom (H := H) (U := X) X hXNormalIn
    have hc2 : 2 ≤ c := by
      by_contra hc
      exact no_chiefSeries_le_one_U_of_caseII hF hB ha hSz hL2 hII hBc hZ2 hser (by omega)
    have hc0 : c = 0 := by
      have h1 : F112W.eta H X X = c := (F112W.isChiefSeriesFrom_iff_eta hXH hXNormalIn).mp hser
      have h2 : F112W.eta H X X = 0 :=
        (F112W.eta_eq_zero_iff hXH hXpc hXNormalIn).mpr hcomm
      omega
    omega
  have hJ2 : ¬ thompsonJ S ≤ Q2 L1 L2 S :=
    not_thompsonJ_le_Q2_of_caseII hF hB hB1 hII
  obtain ⟨A, hAmax, hAnQ2⟩ :=
    CFSG.Quasithin.Ch3g316.exists_isMaxElemAbelian_not_le_pCoreOf (T := S) (Q := Q2 L1 L2 S) hJ2
  have hAS : A ≤ S := hAmax.1
  have hAe : IsElemAbelian 2 A := hAmax.2.1
  obtain ⟨t, htA, htQ2⟩ : ∃ t, t ∈ A ∧ t ∉ Q2 L1 L2 S := by
    by_contra h
    exact hAnQ2 fun x hx => by
      by_contra hxQ
      exact h ⟨x, hx, hxQ⟩
  set B : Subgroup G := A ⊓ Q2 L1 L2 S with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBS : B ≤ S := hBA.trans hAS
  have hBe : IsElemAbelian 2 B := IsElemAbelian.mono hAe hBA
  have hCA : A ⊓ Subgroup.centralizer (X : Set G) =
      B ⊓ Subgroup.centralizer (X : Set G) := by
    refine le_antisymm ?_ (inf_le_inf hBA le_rfl)
    intro a ha
    have haQ2 : a ∈ Q2 L1 L2 S := by
      apply hCX
      refine ⟨?_, ha.2⟩
      rw [hHdef]
      exact (le_sup_right : S ≤ L2 ⊔ S) (hAS ha.1)
    exact ⟨⟨ha.1, haQ2⟩, ha.2⟩
  have hArel : B.relIndex A ≤ 2 ^ (2 * a + 1) := by
    rw [hBdef, Subgroup.inf_relIndex_left]
    calc (Q2 L1 L2 S).relIndex A ≤ (Q2 L1 L2 S).relIndex S :=
          Subgroup.relIndex_le_of_le_right hAS (D15Proof.relIndex_ne_zero _ _)
      _ = 2 ^ (2 * a + 1) := by
          have h := str86_relIndex_q2_s (n := 2 * a + 1) hF hB (by omega) hL2
          simpa using h
  have hQquad : ∀ h ∈ H, ∀ E : Subgroup G, E ≤ B →
      ¬ E ≤ Subgroup.centralizer (cjSub h V : Set G) →
      ((Subgroup.centralizer (cjSub h V : Set G)).relIndex E) ^ 2 ≤
        (Subgroup.centralizer (E : Set G)).relIndex (cjSub h V) := by
    intro h hh E hEB hEnc
    have hEA : E ≤ A := hEB.trans hBA
    have hEe : IsElemAbelian 2 E := IsElemAbelian.mono hAe hEA
    set E' : Subgroup G := cjSub h⁻¹ E with hE'def
    have hh' : h⁻¹ ∈ H := H.inv_mem hh
    have hE'Q2 : E' ≤ Q2 L1 L2 S := by
      rw [hE'def]
      exact cjSub_le (Subgroup.inv_mem _ ((le_normalizer_pCoreOf 2 (P2 L1 L2 S)) (hHleP2 hh)))
        (hEB.trans (hBdef.le.trans inf_le_right))
    have hE'S : E' ≤ S := hE'Q2.trans hQ2S
    have hE'e : IsElemAbelian 2 E' := by
      rw [hE'def]; exact isElemAbelian_cjSub hEe
    have hE'Q1 : ¬ E' ≤ Q1 L1 L2 S := by
      intro hle
      apply hEnc
      have hCV : E' ≤ Subgroup.centralizer (V : Set G) :=
        hle.trans (Q1_le_centralizer_Z1 L1 L2 S)
      have hconj : cjSub h E' ≤ Subgroup.centralizer (cjSub h V : Set G) := by
        rw [← cjSub_centralizer h V]
        exact cjSub_mono hCV
      rwa [show cjSub h E' = E by rw [hE'def]; exact cjSub_cjSub_inv h E] at hconj
    obtain ⟨u, huE', huQ1⟩ : ∃ u, u ∈ E' ∧ u ∉ Q1 L1 L2 S := by
      by_contra h
      exact hE'Q1 fun x hx => by
        by_contra hxQ
        exact h ⟨x, hx, hxQ⟩
    have huS : u ∈ S := hE'S huE'
    have hu2 : u * u ∈ Q1 L1 L2 S := by
      rw [show u * u = 1 from by rw [← pow_two]; exact hE'e.2 u huE']
      exact (Q1 L1 L2 S).one_mem
    have hdispU := hM7 u huS hu2 huQ1
    have hM5E : (E' ⊓ Q1 L1 L2 S).relIndex E' ≤ 2 ^ (2 * a + 1) :=
      hM5 E' hE'S (fun x hx => by rw [← pow_two]; exact hE'e.2 x hx)
    have hCVE : E' ⊓ Q1 L1 L2 S ≤ E' ⊓ Subgroup.centralizer (V : Set G) :=
      inf_le_inf_left E' (Q1_le_centralizer_Z1 L1 L2 S)
    have hrelCV : (E' ⊓ Subgroup.centralizer (V : Set G)).relIndex E' ≤
        (E' ⊓ Q1 L1 L2 S).relIndex E' :=
      Subgroup.relIndex_le_of_le_left hCVE (D15Proof.relIndex_ne_zero _ _)
    have hbq : (Subgroup.centralizer (Z1 L1 L2 S : Set G)).relIndex E' ≤
        2 ^ (2 * a + 1) := by
      rw [← Subgroup.inf_relIndex_left E' (Subgroup.centralizer (Z1 L1 L2 S : Set G))]
      exact hrelCV.trans hM5E
    have hmonoU : (Z1 L1 L2 S ⊓ Subgroup.centralizer ({u} : Set G)).relIndex
        (Z1 L1 L2 S) ≤
        (Subgroup.centralizer (E' : Set G)).relIndex (Z1 L1 L2 S) := by
      rw [← Subgroup.inf_relIndex_left (Z1 L1 L2 S) (Subgroup.centralizer (E' : Set G))]
      exact Subgroup.relIndex_le_of_le_left
        (inf_le_inf_left (Z1 L1 L2 S)
          (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huE')))
        (D15Proof.relIndex_ne_zero _ _)
    have hsq : ((Subgroup.centralizer (Z1 L1 L2 S : Set G)).relIndex E') ^ 2 ≤
        (Subgroup.centralizer (E' : Set G)).relIndex (Z1 L1 L2 S) :=
      (Nat.pow_le_pow_left hbq 2).trans (hdispU.trans hmonoU)
    have hEeq : E = cjSub h E' := by rw [hE'def, cjSub_cjSub_inv]
    calc ((Subgroup.centralizer (cjSub h V : Set G)).relIndex E) ^ 2
        = ((Subgroup.centralizer (V : Set G)).relIndex E') ^ 2 := by
          rw [hEeq, relIndex_centralizer_cjSub h V E']
      _ = ((Subgroup.centralizer (Z1 L1 L2 S : Set G)).relIndex E') ^ 2 := by
          simp [hVdef]
      _ ≤ (Subgroup.centralizer (E' : Set G)).relIndex (Z1 L1 L2 S) := hsq
      _ = (Subgroup.centralizer (E' : Set G)).relIndex V := by simp [hVdef]
      _ = (Subgroup.centralizer (E : Set G)).relIndex (cjSub h V) := by
          rw [hEeq, relIndex_centralizer_cjSub h E' V]
  have hquadB := Ch3y.sq_relIndex_le_nonstrict (V := V) (H := H) (B := B) hQquad B le_rfl
  have hquadB' : ((B ⊓ Subgroup.centralizer (X : Set G)).relIndex B) ^ 2 ≤
      (Subgroup.centralizer (B : Set G)).relIndex X := by
    rw [Subgroup.inf_relIndex_left]
    simpa [hXdef] using hquadB
  have hXCA_le : (Subgroup.centralizer (A : Set G)).relIndex X ≤
      (Subgroup.centralizer (X : Set G)).relIndex A :=
    CFSG.Quasithin.Ch3g316.relIndex_centralizer_le hAmax (hXQ2.trans hQ2S) hXe
  have hXCA_le' : (Subgroup.centralizer (A : Set G)).relIndex X ≤
      (A ⊓ Subgroup.centralizer (X : Set G)).relIndex A := by
    rw [Subgroup.inf_relIndex_left]
    exact hXCA_le
  have hAlphaBeta : (A ⊓ Subgroup.centralizer (X : Set G)).relIndex A =
      (B ⊓ Subgroup.centralizer (X : Set G)).relIndex B * B.relIndex A := by
    rw [hCA]
    exact (Subgroup.relIndex_mul_relIndex (B ⊓ Subgroup.centralizer (X : Set G)) B A
      inf_le_left hBA).symm
  have hmonoCA : (Subgroup.centralizer (B : Set G)).relIndex X ≤
      (Subgroup.centralizer (A : Set G)).relIndex X :=
    Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le hBA)
      (D15Proof.relIndex_ne_zero _ _)
  have hbeta_le : (B ⊓ Subgroup.centralizer (X : Set G)).relIndex B ≤ B.relIndex A := by
    have h1 : (B ⊓ Subgroup.centralizer (X : Set G)).relIndex B *
        (B ⊓ Subgroup.centralizer (X : Set G)).relIndex B ≤
        B.relIndex A * (B ⊓ Subgroup.centralizer (X : Set G)).relIndex B := by
      calc (B ⊓ Subgroup.centralizer (X : Set G)).relIndex B *
            (B ⊓ Subgroup.centralizer (X : Set G)).relIndex B
          = ((B ⊓ Subgroup.centralizer (X : Set G)).relIndex B) ^ 2 := by ring
        _ ≤ (Subgroup.centralizer (B : Set G)).relIndex X := hquadB'
        _ ≤ (Subgroup.centralizer (A : Set G)).relIndex X := hmonoCA
        _ ≤ (A ⊓ Subgroup.centralizer (X : Set G)).relIndex A := hXCA_le'
        _ = (B ⊓ Subgroup.centralizer (X : Set G)).relIndex B * B.relIndex A := hAlphaBeta
        _ = B.relIndex A * (B ⊓ Subgroup.centralizer (X : Set G)).relIndex B := by ring
    exact Nat.le_of_mul_le_mul_right h1
      (Nat.pos_of_ne_zero (D15Proof.relIndex_ne_zero _ _))
  have hAlphaBeta_le : (A ⊓ Subgroup.centralizer (X : Set G)).relIndex A ≤
      (2 ^ (2 * a + 1)) ^ 2 := by
    rw [hAlphaBeta]
    calc (B ⊓ Subgroup.centralizer (X : Set G)).relIndex B * B.relIndex A
        ≤ (2 ^ (2 * a + 1)) * (2 ^ (2 * a + 1)) :=
          Nat.mul_le_mul (hbeta_le.trans hArel) hArel
      _ = (2 ^ (2 * a + 1)) ^ 2 := by ring
  have hXCA_le_q2 : (Subgroup.centralizer (A : Set G)).relIndex X ≤
      (2 ^ (2 * a + 1)) ^ 2 := hXCA_le'.trans hAlphaBeta_le
  have htH : t ∈ H := hSH (hAS htA)
  have ht2 : t * t ∈ pCoreOf 2 H := by
    rw [hpCore2]
    rw [show t * t = 1 from by rw [← pow_two]; exact hAe.2 t htA]
    exact (Q2 L1 L2 S).one_mem
  have htO : t ∉ pCoreOf 2 H := by rw [hpCore2]; exact htQ2
  have hTbound : (Subgroup.centralizer ({t} : Set G)).relIndex X ≤
      (2 ^ (2 * a + 1)) ^ 2 :=
    (Subgroup.relIndex_le_of_le_left
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htA))
      (D15Proof.relIndex_ne_zero _ _)).trans hXCA_le_q2
  have hCount : ∀ c : ℕ, IsChiefSeriesFrom H X X c → c = 2 := by
    intro c hser
    have hc2 : 2 ≤ c := by
      by_contra hc
      exact no_chiefSeries_le_one_U_of_caseII hF hB ha hSz hL2 hII hBc hZ2 hser (by omega)
    have hM6 := l2_pow_sq_le_relIndex_centralizer (H := H) (U := X)
      (m := 2 * a + 1) (c := c) (by omega) hL2H hX2 hXH hser htH ht2 htO
    have hcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
        Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcent] at hM6
    have hpow : (2 ^ (2 * a + 1)) ^ c ≤ (2 ^ (2 * a + 1)) ^ 2 :=
      hM6.trans hTbound
    exact le_antisymm ((Nat.pow_le_pow_iff_right hq1).mp hpow) hc2
  refine ⟨by simpa [hHdef, hVdef, hXdef] using hXe,
    by simpa [hHdef, hVdef, hXdef] using le_inf hXQ1 hXQ2, hCount, ?_⟩
  intro L N hstep hUH hnc hE
  let e₀ : oTwoQuot ↥H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (2 * a + 1)) :=
    Classical.choice hL2H
  let e : oTwoQuot ↥H ≃* SL(2, GaloisField 2 (2 * a + 1)) :=
    e₀.trans (CFSG.CGT.Timmesfeld75.pslMulEquivSL (F := GaloisField 2 (2 * a + 1)))
  refine ⟨e, ?_⟩
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  let ρ := l2ChiefSectionRep hstep hUH hE e
  change CFSG.QuasithinUnique.Setup.SL2Modules.IsNaturalModule ρ
  obtain ⟨c, hser⟩ := D15Proof.exists_isChiefSeriesFrom (H := H) (U := X) X hXNormalIn
  have hc : c = 2 := hCount c hser
  have hlower : 2 ^ (2 * a + 1) ≤
      (centralizerMod L N (Subgroup.zpowers t)).relIndex N :=
    l2ChiefSectionRep_pow_le_relIndex_centralizerMod (m := 2 * a + 1) (by omega) hL2H
      hX2 hXH hstep hnc htH ht2 htO
  have hupper : (centralizerMod L N (Subgroup.zpowers t)).relIndex N ≤
      2 ^ (2 * a + 1) := by
    have hb := Ch3y.step_bound (H := H) (U := X) (A := Subgroup.zpowers t) hXH
      (Subgroup.zpowers_le.mpr htH) (k := 2 ^ (2 * a + 1))
      (fun L' N' hstep' hnc' =>
        l2ChiefSectionRep_pow_le_relIndex_centralizerMod (m := 2 * a + 1) (by omega)
          hL2H hX2 hXH hstep' hnc' htH ht2 htO)
      hstep hnc hser
    rw [hc] at hb
    rw [pow_one] at hb
    have hcent : Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G) =
        Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcent] at hb
    have hqd : (centralizerMod L N (Subgroup.zpowers t)).relIndex N * 2 ^ (2 * a + 1) ≤
        2 ^ (2 * a + 1) * 2 ^ (2 * a + 1) := by
      rw [mul_comm]
      simpa [pow_two] using hb.trans hTbound
    exact Nat.le_of_mul_le_mul_right hqd (by positivity)
  have hd : (centralizerMod L N (Subgroup.zpowers t)).relIndex N = 2 ^ (2 * a + 1) :=
    le_antisymm hupper hlower
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hXH).trans hHL
  haveI : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hstep.2.2.1.le).mpr hNL
  let a' : SL(2, GaloisField 2 (2 * a + 1)) := e (QuotientGroup.mk ⟨t, htH⟩)
  have hsqfix : Nat.card (CFSG.RankThree.FFModules.fixSub ρ
      (Subgroup.zpowers a')) ^ 2 = Nat.card (Additive (Ch3z.chiefMod L N)) :=
    l2ChiefSectionRep_sq_card_fixSub (by omega) hstep hUH hE e hnc htH ht2 htO
  have hfixcard : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) =
      Nat.card (CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers a')) := by
    rw [show ρ = (CFSG.RankThree.FFModules.autRep (Ch3z.chiefMod L N)).comp
      (l2ChiefSectionSL2Action hstep hUH hE e) from rfl]
    rw [CFSG.RankThree.FFModules.card_fixSub_autRep_comp
      (E := Ch3z.chiefMod L N) (ι := l2ChiefSectionSL2Action hstep hUH hE e)
      (B := Subgroup.zpowers a')]
    congr 1
    rw [MonoidHom.map_zpowers]
    congr 1
    rw [l2ChiefSectionSL2Action_apply, MulEquiv.symm_apply_apply, l2ChiefSectionQuotAction_mk]
  let K : Subgroup (SectionW N L) :=
    (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).comap
      (Ch3z.chiefQuotEquiv hNL).toMonoidHom
  have hKmem : ∀ u : ↥N, QuotientGroup.mk u ∈ K ↔
      l2SectionAction hstep hUH ⟨t, htH⟩ (QuotientGroup.mk u) = QuotientGroup.mk u := by
    intro u
    constructor
    · intro hu
      have hu' : l2ChiefSectionAction hstep hE ⟨t, htH⟩
          (Ch3z.chiefQuotEquiv hNL (QuotientGroup.mk u)) =
          Ch3z.chiefQuotEquiv hNL (QuotientGroup.mk u) :=
        mem_fixV_zpowers_iff_apply.mp hu
      apply (Ch3z.chiefQuotEquiv hNL).injective
      rw [chiefQuotEquiv_l2SectionAction (hE := hE), hu']
    · intro hu
      have h2 := congrArg (Ch3z.chiefQuotEquiv hNL) hu
      rw [chiefQuotEquiv_l2SectionAction (hE := hE)] at h2
      exact mem_fixV_zpowers_iff_apply.mpr h2
  have hact : ∀ u : ↥N, l2SectionAction hstep hUH ⟨t, htH⟩ (QuotientGroup.mk u) =
      QuotientGroup.mk (conjAct N ⟨t, hHN htH⟩ u) :=
    fun u => l2SectionAction_mk hstep hUH ⟨t, htH⟩ u
  have hidx := relIndex_centralizerMod_eq_index_of_fixedSection hHN hHL htH hNL
    (l2SectionAction hstep hUH ⟨t, htH⟩) K hKmem hact
  have hKindex : K.index =
      (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index :=
    Subgroup.index_comap_of_surjective _ (Ch3z.chiefQuotEquiv hNL).surjective
  have hcardfix : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) *
      (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index =
      Nat.card (Ch3z.chiefMod L N) :=
    Subgroup.card_mul_index _
  have hW : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) ^ 2 =
      Nat.card (Ch3z.chiefMod L N) := by
    rw [hfixcard]
    exact hsqfix.trans (Nat.card_congr Additive.ofMul).symm
  have hfixpos : 0 <
      Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
    by_contra h0
    have h0' : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) = 0 :=
      Nat.eq_zero_of_not_pos h0
    rw [h0', zero_pow (by norm_num)] at hW
    exact (Nat.card_pos (α := Ch3z.chiefMod L N)).ne' hW.symm
  have hidxfix : (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index =
      Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
    have h2 : Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) *
        (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))).index =
        Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) *
        Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
      rw [hcardfix, ← hW, pow_two]
    exact Nat.eq_of_mul_eq_mul_left hfixpos h2
  have hd_eq : (centralizerMod L N (Subgroup.zpowers t)).relIndex N =
      Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) := by
    rw [hidx, hKindex, hidxfix]
  have hWcard : Nat.card (Additive (Ch3z.chiefMod L N)) = (2 ^ (2 * a + 1)) ^ 2 := by
    calc Nat.card (Additive (Ch3z.chiefMod L N))
        = Nat.card (CFSG.RankThree.FFModules.fixSub ρ (Subgroup.zpowers a')) ^ 2 :=
          hsqfix.symm
      _ = Nat.card (fixV (Subgroup.zpowers (l2ChiefSectionAction hstep hE ⟨t, htH⟩))) ^ 2 := by
          rw [← hfixcard]
      _ = (centralizerMod L N (Subgroup.zpowers t)).relIndex N ^ 2 := by rw [← hd_eq]
      _ = (2 ^ (2 * a + 1)) ^ 2 := by rw [hd]
  haveI : Fintype (GaloisField 2 (2 * a + 1)) := Fintype.ofFinite _
  have hm : 1 ≤ 2 * a + 1 := by omega
  have hcardGF : Fintype.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card 2 (2 * a + 1) (by omega)
  have hlt : Nat.card (Additive (Ch3z.chiefMod L N)) < 2 ^ (4 * (2 * a + 1)) := by
    rw [hWcard, ← pow_mul]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hnt : ∃ g, ρ g ≠ 1 := l2ChiefSectionRep_nontrivial hstep hUH hE e hnc
  haveI : Fact ρ.IsIrreducible := ⟨l2ChiefSectionRep_irreducible hstep hUH hE e⟩
  have hA2 : ∀ x ∈ CFSG.CGT.Timmesfeld75.utri (GaloisField 2 (2 * a + 1)), x * x = 1 := by
    intro x hx
    obtain ⟨s, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_utri_iff.mp hx
    exact CFSG.CGT.Timmesfeld75.utriElt_mul_self s
  have hAcard : Nat.card (CFSG.CGT.Timmesfeld75.utri (GaloisField 2 (2 * a + 1))) =
      2 ^ (2 * a + 1) := by
    rw [CFSG.CGT.Timmesfeld75.card_utri, Nat.card_eq_fintype_card, hcardGF]
  rcases isNaturalModule_or_isOrthModule_or_of_card_lt hm hcardGF ρ hnt
    (CFSG.CGT.Timmesfeld75.utri (GaloisField 2 (2 * a + 1))) hA2 hAcard hlt with
    hnat | horth | hthird
  · exact hnat
  · obtain ⟨l, -, hm2l, -⟩ := horth
    omega
  · obtain ⟨l, hm3l, hW8, -⟩ := hthird
    have hWq : Nat.card (Additive (Ch3z.chiefMod L N)) = 2 ^ (2 * (2 * a + 1)) := by
      rw [hWcard, ← pow_mul, mul_comm (2 * a + 1) 2]
    rw [hWq] at hW8
    have hEq : 2 * (2 * a + 1) = 8 * l :=
      Nat.pow_right_injective (by norm_num) hW8
    omega

end CFSG.Quasithin.Stroth

end
