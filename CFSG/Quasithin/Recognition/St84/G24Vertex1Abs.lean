module

public import CFSG.Quasithin.Recognition.St84.G24Vertex1Model
public import CFSG.Quasithin.Recognition.St84.G24Vertex1Action
public import CFSG.Quasithin.Recognition.J2RecAmalgam
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.GroupTheory
open CFSG.Quasithin.KGC31 (eElt)
open CFSG.GroupTheory (eElt_mem_of_forall_mem)
open Certificates.A5GL42 (aO bO)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem G24Vertex1.card_A_inf_L1 [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD : G24LocalData L1 L2 S) {k : G}
    (hdec : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L1 L2 S,
      ∃ c ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G), x = q * c)
    (hcardA : Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer ({k} : Set G)) = 180) :
    Nat.card ↥(((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)) ⊓ L1) = 60 := by
  let A : Subgroup G := (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)
  change Nat.card ↥(A ⊓ L1) = 60
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQL : dsQ L1 L2 S ≤ L1 := by
    have h := G24LocalData.pCoreOf_eq_dsQ_left hR hD.le_left
    rw [← h]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 L1
  have hsupAQ : dsQ L1 L2 S ⊔ A = L1 ⊔ bigB L1 L2 S := by
    refine le_antisymm (sup_le (dsQ_le_P_left L1 L2 S) inf_le_left) ?_
    intro x hx
    obtain ⟨q, hq, c, hc, rfl⟩ := hdec x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hq)
      (Subgroup.mem_sup_right (show c ∈ A from hc))
  have hsup : L1 ⊔ A = L1 ⊔ bigB L1 L2 S := by
    refine le_antisymm (sup_le le_sup_left inf_le_left) ?_
    rw [← hsupAQ]
    refine sup_le ?_ ?_
    · exact hQL.trans (le_sup_left : L1 ≤ L1 ⊔ A)
    · exact le_sup_right
  have hnorm : A ≤ Subgroup.normalizer (L1 : Set G) :=
    inf_le_left.trans (G24LocalData.normal_L_left hR)
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := L1) (B := A) hnorm
  rw [hsup, G24LocalData.card_vertex_left hF h1 hD, G24LocalData.card_L_left hF h1 hD,
    hD.card_dsQ_left] at hcard
  rw [hcardA] at hcard
  norm_num at hcard
  rw [inf_comm]
  change Nat.card {x // x ∈ L1 ∧ x ∈ A} = 60
  omega

theorem G24Vertex1.isSimpleGroup_inter_centralizer_L1 [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1)
    (hD : G24LocalData L1 L2 S) {k : G}
    (hinf : dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) = ⊥)
    (hBcard : Nat.card ↥(((L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer ({k} : Set G)) ⊓ L1) = 60) :
    IsSimpleGroup ↥(((L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer ({k} : Set G)) ⊓ L1) := by
  let A : Subgroup G := (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)
  let B : Subgroup G := A ⊓ L1
  change IsSimpleGroup ↥B
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hQeq : pCoreOf 2 L1 = dsQ L1 L2 S := G24LocalData.pCoreOf_eq_dsQ_left hR hD.le_left
  have hAQ : A ⊓ dsQ L1 L2 S = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : x ∈ dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) :=
      ⟨hx.2, (show A ≤ Subgroup.centralizer ({k} : Set G) from inf_le_right) hx.1⟩
    rw [hinf] at hx'
    exact Subgroup.mem_bot.mp hx'
  have hBQ : B ⊓ dsQ L1 L2 S = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : x ∈ A ⊓ dsQ L1 L2 S := ⟨(show B ≤ A from inf_le_left) hx.1, hx.2⟩
    rw [hAQ] at hx'
    exact Subgroup.mem_bot.mp hx'
  have hBL1 : B ≤ L1 := inf_le_right
  let φ : ↥B →* oTwoQuot ↥L1 :=
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥L1)).comp (Subgroup.inclusion hBL1)
  have hker : φ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_bot]
    have hbP : Subgroup.inclusion hBL1 b ∈ CFSG.Open.pCore 2 ↥L1 :=
      (QuotientGroup.eq_one_iff _).mp hb
    have hbQ : (b : G) ∈ dsQ L1 L2 S := by
      rw [← hQeq]
      exact ⟨Subgroup.inclusion hBL1 b, hbP, rfl⟩
    have hmem : (b : G) ∈ B ⊓ dsQ L1 L2 S := ⟨b.2, hbQ⟩
    rw [hBQ] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker
  have hquotcard : Nat.card (oTwoQuot ↥L1) = 60 := by
    rw [CFSG.Quasithin.IsL2Quot.card (by norm_num : 1 ≤ 2) h1]
    norm_num
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_injective_and_card φ).mpr ⟨hinj, by rw [hBcard, hquotcard]⟩
  let e : ↥B ≃* oTwoQuot ↥L1 := MulEquiv.ofBijective φ hbij
  haveI : IsSimpleGroup (oTwoQuot ↥L1) := by
    obtain ⟨e5⟩ := CFSG.Quasithin.S1421QA17.nonempty_mulEquiv_alt5_of_isL2Quot_two h1
    exact e5.isSimpleGroup
  exact e.isSimpleGroup

private theorem closure_pair_eq_inter [Finite G]
    {L1 L2 S E : Subgroup G} (hF : F112HypW L1 L2 S)
    (h1 : VA5 L1) (hD : G24LocalData L1 L2 S) {k a b : G}
    (hdec : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L1 L2 S,
      ∃ c ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G), x = q * c)
    (hcardA : Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer ({k} : Set G)) = 180)
    (hinf : dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) = ⊥)
    {M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S)) Certificates.A5GL42.HO}
    (haA : a ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G))
    (hbA : b ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G))
    (haL : a ∈ L1) (hbL : b ∈ L1)
    (hMa : glMat (M.F.M ⟨a, haL⟩) = aO) (hMb : glMat (M.F.M ⟨b, hbL⟩) = bO)
    (hb3 : b ^ 3 = 1) (hab5 : (a * b) ^ 5 = 1) :
    Subgroup.closure ({a, b} : Set G) =
      ((L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)) ⊓ L1 := by
  let A : Subgroup G := (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)
  let B : Subgroup G := A ⊓ L1
  let C : Subgroup G := Subgroup.closure ({a, b} : Set G)
  change C = B
  have hCB : C ≤ B := by
    change Subgroup.closure ({a, b} : Set G) ≤ B
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨haA, haL⟩
    · exact ⟨hbA, hbL⟩
  have haC : a ∈ C := Subgroup.subset_closure (by simp)
  have hbC : b ∈ C := Subgroup.subset_closure (by simp)
  have habC : a * b ∈ C := C.mul_mem haC hbC
  have hb_ne : b ≠ 1 := by
    intro h
    have h1 : M.F.M ⟨b, hbL⟩ = 1 := by
      rw [show (⟨b, hbL⟩ : ↥L1) = 1 from Subtype.ext h, map_one]
    have : bO = 1 := by rw [← hMb, h1]; rfl
    exact (by decide : bO ≠ 1) this
  have habL : a * b ∈ L1 := L1.mul_mem haL hbL
  have hMab : glMat (M.F.M ⟨a * b, habL⟩) = aO * bO := by
    have hsub : (⟨a * b, habL⟩ : ↥L1) = ⟨a, haL⟩ * ⟨b, hbL⟩ := rfl
    rw [hsub, map_mul]
    change glMat (M.F.M ⟨a, haL⟩) * glMat (M.F.M ⟨b, hbL⟩) = aO * bO
    rw [hMa, hMb]
  have hab_ne : a * b ≠ 1 := by
    intro h
    have h1 : M.F.M ⟨a * b, habL⟩ = 1 := by
      rw [show (⟨a * b, habL⟩ : ↥L1) = 1 from Subtype.ext h, map_one]
    have : aO * bO = 1 := by rw [← hMab, h1]; rfl
    exact (by decide : aO * bO ≠ 1) this
  have hord_b : orderOf b = 3 := orderOf_eq_prime hb3 hb_ne
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord_ab : orderOf (a * b) = 5 := orderOf_eq_prime hab5 hab_ne
  have h3dvd : 3 ∣ Nat.card ↥C := by
    have h := orderOf_dvd_natCard (⟨b, hbC⟩ : ↥C)
    rw [Subgroup.orderOf_mk, hord_b] at h
    exact h
  have h5dvd : 5 ∣ Nat.card ↥C := by
    have h := orderOf_dvd_natCard (⟨a * b, habC⟩ : ↥C)
    rw [Subgroup.orderOf_mk, hord_ab] at h
    exact h
  have h15dvd : 15 ∣ Nat.card ↥C := by
    have h := (by norm_num : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd h3dvd h5dvd
    simpa using h
  have hBcard : Nat.card ↥B = 60 := by
    have h := G24Vertex1.card_A_inf_L1 hF h1 hD hdec hcardA
    change Nat.card ↥(A ⊓ L1) = 60 at h
    exact h
  have hXcard : Nat.card ↥(C.subgroupOf B) = Nat.card ↥C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv
  have h15 : 15 ∣ Nat.card ↥(C.subgroupOf B) := by
    rwa [hXcard]
  haveI : IsSimpleGroup ↥B := G24Vertex1.isSimpleGroup_inter_centralizer_L1 hF h1 hD hinf hBcard
  have htop : C.subgroupOf B = ⊤ := subgroup_eq_top_of_fifteen_dvd hBcard h15
  have hCB_eq : C = B := le_antisymm hCB (Subgroup.subgroupOf_eq_top.mp htop)
  exact hCB_eq

theorem G24Vertex1.closure_a_b_k_eq [Finite G]
    {L1 L2 S E : Subgroup G} (hF : F112HypW L1 L2 S)
    (h1 : VA5 L1) (hD : G24LocalData L1 L2 S) {k a b : G}
    (hkB : k ∈ bigB L1 L2 S) (hk3 : orderOf k = 3) (hkL : k ∉ L1)
    (hdec : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ∃ q ∈ dsQ L1 L2 S,
      ∃ c ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G), x = q * c)
    (hcardA : Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer ({k} : Set G)) = 180)
    (hinf : dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) = ⊥)
    {M : A5Model L1 L1 E (centerOf (dsQ L1 L2 S)) Certificates.A5GL42.HO}
    (haA : a ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G))
    (hbA : b ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G))
    (haL : a ∈ L1) (hbL : b ∈ L1)
    (hMa : glMat (M.F.M ⟨a, haL⟩) = aO) (hMb : glMat (M.F.M ⟨b, hbL⟩) = bO)
    (hb3 : b ^ 3 = 1) (hab5 : (a * b) ^ 5 = 1) :
    Subgroup.closure ({a, b, k} : Set G) =
      (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) := by
  let A : Subgroup G := (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G)
  let B : Subgroup G := A ⊓ L1
  let C : Subgroup G := Subgroup.closure ({a, b} : Set G)
  change Subgroup.closure ({a, b, k} : Set G) = A
  have hBL1 : B ≤ L1 := inf_le_right
  have hBA : B ≤ A := inf_le_left
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hCB_eq : C = B := by
    change Subgroup.closure ({a, b} : Set G) = A ⊓ L1
    exact closure_pair_eq_inter hF h1 hD hdec hcardA hinf haA hbA haL hbL hMa hMb hb3 hab5
  have hBcard : Nat.card ↥B = 60 := by
    have h := G24Vertex1.card_A_inf_L1 hF h1 hD hdec hcardA
    change Nat.card ↥(A ⊓ L1) = 60 at h
    exact h
  have hkA : k ∈ A := by
    refine ⟨(le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hkB, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  have hBK_le_A : B ⊔ Subgroup.zpowers k ≤ A :=
    sup_le hBA (Subgroup.zpowers_le.mpr hkA)
  have hdisj : Disjoint B (Subgroup.zpowers k) :=
    (disjoint_iff.mpr (GL83.CompFam.inf_zpowers_eq_bot hk3 hkL)).mono_left hBL1
  have hKnorm : Subgroup.zpowers k ≤ Subgroup.normalizer (B : Set G) := by
    have hAN : A ≤ Subgroup.normalizer (B : Set G) := by
      have h1' : A ≤ Subgroup.normalizer (A : Set G) := Subgroup.le_normalizer
      have h2' : A ≤ Subgroup.normalizer (L1 : Set G) :=
        (show A ≤ L1 ⊔ bigB L1 L2 S from inf_le_left).trans (G24LocalData.normal_L_left hR)
      exact (le_inf h1' h2').trans Subgroup.inf_normalizer_le_normalizer_inf
    exact (Subgroup.zpowers_le.mpr hkA).trans hAN
  have hBsup : Nat.card ↥(B ⊔ Subgroup.zpowers k) = 60 * 3 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer B
      (Subgroup.zpowers k) hKnorm hdisj, hBcard, Nat.card_zpowers, hk3]
  have hBK_eq_A : B ⊔ Subgroup.zpowers k = A := by
    refine Subgroup.eq_of_le_of_card_ge hBK_le_A ?_
    rw [hBsup, hcardA]
  have hcl : Subgroup.closure ({a, b, k} : Set G) = C ⊔ Subgroup.zpowers k := by
    rw [show ({a, b, k} : Set G) = {a, b} ∪ {k} by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto]
    rw [Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
  rw [hcl, hCB_eq, hBK_eq_A]

theorem exists_g24Frame1 [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (h1 : VA5 L1) (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) {k : G}
    (hkB : k ∈ bigB L1 L2 S) (hk3 : orderOf k = 3) (hkL : k ∉ L1)
    (hkc : ∀ x ∈ L1 ⊔ bigB L1 L2 S, ⁅k, x⁆ ∈ dsQ L1 L2 S) :
    ∃ F : G24Frame1 L1 L2 S, F.k = k := by
  let hQZ := (dsQ_le_P_left L1 L2 S).trans
    (P_le_normalizer_centerOf_dsQ_left L1 L2 S)
  have hXeq : fixedModSubgroup (dsQ L1 L2 S) (centerOf (dsQ L1 L2 S)) k hQZ =
      centerOf (dsQ L1 L2 S) :=
    G24Vertex1.fixedModSubgroup_eq_centerOf hF h1 h2 hD hkB hk3 hkL hkc
  have hfix : ∀ x ∈ dsQ L1 L2 S,
      k * x * k⁻¹ * x⁻¹ ∈ centerOf (dsQ L1 L2 S) → x ∈ centerOf (dsQ L1 L2 S) := by
    intro x hx hxZ
    have hxX : x ∈ fixedModSubgroup (dsQ L1 L2 S) (centerOf (dsQ L1 L2 S)) k hQZ := by
      rw [CFSG.GroupTheory.mem_fixedModSubgroup]
      exact ⟨hx, hxZ⟩
    rwa [hXeq] at hxX
  have hinf : dsQ L1 L2 S ⊓ Subgroup.centralizer ({k} : Set G) = ⊥ :=
    G24Vertex1.inf_centralizer_eq_bot hF h1 h2 hD hkB hk3 hkL hfix
  have hdec := G24Vertex1.exists_mul_centralizer hD hkB hk3 hkc
  have hcardA : Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓
      Subgroup.centralizer ({k} : Set G)) = 180 :=
    G24Vertex1.card_centralizer hF h1 hD hdec hinf
  obtain ⟨E, M, hZE, hEQ, hrel, hL1E, hntriv, hnat⟩ :=
    G24Vertex1.exists_a5model hF h1 hD
  obtain ⟨a, b, haA, hbA, haL, hbL, hMa, hMb, ha2, hb3, hab5⟩ :=
    G24Vertex1.exists_a_b_of_model hF hD hdec hinf (E := E) (M := M)
  let e : Fin 4 → G := fun j =>
    (Classical.choose (M.F.surj (Multiplicative.ofAdd (Pi.single j (1 : ZMod 2))))).val
  have heE : ∀ j, e j ∈ E := fun j =>
    (Classical.choose (M.F.surj (Multiplicative.ofAdd (Pi.single j (1 : ZMod 2))))).2
  have hephi : ∀ j, M.F.φ ⟨e j, heE j⟩ =
      Multiplicative.ofAdd (Pi.single j (1 : ZMod 2)) := fun j =>
    Classical.choose_spec (M.F.surj (Multiplicative.ofAdd (Pi.single j (1 : ZMod 2))))
  have hinter : E ⊓ E.map (MulAut.conj k).toMonoidHom = centerOf (dsQ L1 L2 S) :=
    G24Vertex1.inter_conj_eq_center hF h1 hD hkB hkL hkc hZE hEQ hrel hL1E hntriv M
  have hindep : ∀ v : Fin 8 → ZMod 2,
      eElt (v1Frame k e) v ∈ centerOf (dsQ L1 L2 S) → v = 0 :=
    G24Vertex1.indep_v1Frame hkB hZE heE hephi hinter
  have hacta : ∀ j : Fin 8, a * v1Frame k e j * a⁻¹ *
      (eElt (v1Frame k e) (fun i => v1Diag aO i j))⁻¹ ∈ centerOf (dsQ L1 L2 S) :=
    G24Vertex1.act_diag_mem hkB hL1E heE hephi haA haL aO (hMa haL)
  have hactb : ∀ j : Fin 8, b * v1Frame k e j * b⁻¹ *
      (eElt (v1Frame k e) (fun i => v1Diag bO i j))⁻¹ ∈ centerOf (dsQ L1 L2 S) :=
    G24Vertex1.act_diag_mem hkB hL1E heE hephi hbA hbL bO (hMb hbL)
  have hactk : ∀ j : Fin 8, k * v1Frame k e j * k⁻¹ *
      (eElt (v1Frame k e) (fun i => v1Omega i j))⁻¹ ∈ centerOf (dsQ L1 L2 S) :=
    G24Vertex1.act_k_mem hD hkB hk3 hfix hEQ heE
  have hclosure : Subgroup.closure ({a, b, k} : Set G) =
      (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.centralizer ({k} : Set G) :=
    G24Vertex1.closure_a_b_k_eq hF h1 hD hkB hk3 hkL hdec hcardA hinf (M := M)
      haA hbA haL hbL (hMa haL) (hMb hbL) hb3 hab5
  refine ⟨{
    k := k
    a := a
    b := b
    e := e
    k_mem := hkB
    k_not_mem := hkL
    orderOf_k := hk3
    comm_k := hkc
    inf_centralizer := hinf
    decomp := hdec
    card_A := hcardA
    a_mem := ⟨haL, haA.2⟩
    b_mem := ⟨hbL, hbA.2⟩
    a_sq := ha2
    b_cube := hb3
    ab_five := hab5
    closure_eq := hclosure
    e_mem := fun i => hEQ (heE i)
    indep := hindep
    act_a := hacta
    act_b := hactb
    act_k := hactk }, rfl⟩

theorem nonempty_g24Frame1 [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S)
    (h1 : VA5 L1) (h2 : VA5 L2) (hD : G24LocalData L1 L2 S) :
    Nonempty (G24Frame1 L1 L2 S) := by
  obtain ⟨k, hkB, hk3, hkL, hkc⟩ := G24LocalData.exists_k_left hF h1 hD
  obtain ⟨F, -⟩ := exists_g24Frame1 hF h1 h2 hD hkB hk3 hkL hkc
  exact ⟨F⟩

end CFSG.Quasithin.F112R.St84
