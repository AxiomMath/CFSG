module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res4ProofS
import CFSG.RankThree.PartTwo.Sec11.Item1118StepsProofChooseG
import CFSG.RankThree.PartTwo.Sec11.Item1125Proof
import CFSG.RankThree.PartTwo.Sec11.Inverter1118ProofInv
public import CFSG.RankThree.PartTwo.Sec11.Inverter1118Proof
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec11.Item1115NotFieldProof
public import CFSG.RankThree.PartTwo.Sec11.Item1116NoFifteen
public import CFSG.RankThree.PartTwo.Sec11.Item1121Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1117Res4Proof

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem conj_inv_mul_mem_of_mem_R (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {j : G}
    (hjL : j ∈ Subgroup.normalizer (L : Set G)) (hjR : j ∈ Subgroup.normalizer (R : Set G))
    (hjx : j * x * j⁻¹ = x⁻¹) (hjs : j * s * j⁻¹ = s⁻¹) :
    ∀ y ∈ R, y⁻¹ * (j * y * j⁻¹) ∈ Subgroup.closure ({s, x} : Set G) := by
  set V := Subgroup.closure ({s, x} : Set G) with hV
  have hRV : R ≤ Subgroup.normalizer (V : Set G) := h.R_le_normalizer_V h45
  have hsV : s ∈ V := Subgroup.subset_closure (by simp)
  have hxV : x ∈ V := Subgroup.subset_closure (by simp)
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  let S : Subgroup G :=
    { carrier := {y | y ∈ R ∧ y⁻¹ * (j * y * j⁻¹) ∈ V}
      one_mem' := ⟨R.one_mem, by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁R, hy₁⟩ ⟨hy₂R, hy₂⟩
        refine ⟨R.mul_mem hy₁R hy₂R, ?_⟩
        have e : (y₁ * y₂)⁻¹ * (j * (y₁ * y₂) * j⁻¹) =
            (y₂⁻¹ * (y₁⁻¹ * (j * y₁ * j⁻¹)) * y₂⁻¹⁻¹) * (y₂⁻¹ * (j * y₂ * j⁻¹)) := by group
        rw [e]
        exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRV (R.inv_mem hy₂R)) _).mp hy₁) hy₂
      inv_mem' := by
        rintro y ⟨hyR, hy⟩
        refine ⟨R.inv_mem hyR, ?_⟩
        have e : y⁻¹⁻¹ * (j * y⁻¹ * j⁻¹) = y * (y⁻¹ * (j * y * j⁻¹))⁻¹ * y⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hRV hyR) _).mp (V.inv_mem hy) }
  have hRS : R ≤ S := by
    rw [Item1116NoFifteen.R_eq_of_closure_eq h hrs, Subgroup.closure_le]
    obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
    rintro y (rfl | rfl | rfl)
    ·
      refine ⟨haR, ?_⟩
      have hI := commutator_mem_innerPreimage outAbelian1016 h.isList1016 hjL
        h.toHyp81.a_mem_normalizer
      have hjaR : j * y * j⁻¹ * y⁻¹ ∈ R :=
        R.mul_mem ((Subgroup.mem_normalizer_iff.mp hjR y).mp haR) (R.inv_mem haR)
      have hmem : j * y * j⁻¹ * y⁻¹ ∈ V := by
        rw [hV, ← h.inf_innerPreimage_eq]
        exact ⟨hjaR, hI⟩
      have e : y⁻¹ * (j * y * j⁻¹) = y⁻¹ * (j * y * j⁻¹ * y⁻¹) * y⁻¹⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hRV (R.inv_mem haR)) _).mp hmem
    · refine ⟨hxR, ?_⟩
      rw [hjx]
      exact V.mul_mem (V.inv_mem hxV) (V.inv_mem hxV)
    · refine ⟨hsR, ?_⟩
      rw [hjs]
      exact V.mul_mem (V.inv_mem hsV) (V.inv_mem hsV)
  exact fun y hy => (hRS hy).2

theorem mem_normalizer_V_of_commute (h45 : Sec4.Item4_5) (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) {j : G}
    (hjL : j ∈ Subgroup.normalizer (L : Set G)) (hjR : j ∈ Subgroup.normalizer (R : Set G))
    (hjx : j * x * j⁻¹ = x⁻¹) (hjs : j * s * j⁻¹ = s⁻¹) {g' : G}
    (hg'R : g' ∈ Subgroup.normalizer (R : Set G)) (hg'j : g' * j = j * g') :
    g' ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) := by
  set V := Subgroup.closure ({s, x} : Set G) with hV
  have hmod := conj_inv_mul_mem_of_mem_R h45 h hrs hjL hjR hjx hjs
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have key : ∀ v ∈ R, j * v * j⁻¹ = v⁻¹ → g' * v * g'⁻¹ ∈ V := by
    intro v hvR hjv
    set y := g' * v * g'⁻¹ with hy
    have hyR : y ∈ R := (Subgroup.mem_normalizer_iff.mp hg'R v).mp hvR
    have hjy : j * y * j⁻¹ = g' * (j * v * j⁻¹) * g'⁻¹ := by
      have hj' : j = g' * j * g'⁻¹ := by rw [hg'j, mul_inv_cancel_right]
      calc j * y * j⁻¹ = (g' * j * g'⁻¹) * y * (g' * j * g'⁻¹)⁻¹ := by rw [← hj']
        _ = g' * (j * v * j⁻¹) * g'⁻¹ := by rw [hy]; group
    have h1 := hmod y hyR
    rw [hjy, hjv] at h1
    have e : y⁻¹ * (g' * v⁻¹ * g'⁻¹) = y ^ (-2 : ℤ) := by
      rw [hy]
      have : g' * v⁻¹ * g'⁻¹ = (g' * v * g'⁻¹)⁻¹ := by group
      rw [this, show (-2 : ℤ) = -1 + -1 by norm_num, zpow_add, zpow_neg_one]
    rw [e] at h1
    have hy3 : ∃ k : ℕ, y ^ 3 ^ k = 1 := Item1116Proof.exists_pow_eq_one_of_mem h hyR
    exact Subgroup.zpowers_le.mpr h1
      (Item1116Proof.mem_zpowers_zpow_of_not_dvd hy3 (by norm_num))
  refine Item1118StepsProof.mem_normalizer_closure_of_forall ?_
  rintro v (rfl | rfl)
  · exact key v hsR hjs
  · exact key v hxR hjx

theorem false_of_normalized (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113)
    (h117 : Item117) (h1120 : Item1120) (hK : KFact1121Lists)
    (hbig : Sec11Big G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hbig.toSec11Data
  have h1115 := item1115_of_mhoV h45 h113 h117
  have hrs := item1123N_of_steps h45 h48 h113 h117 h1115 h1120 hK G A c L a R Y d x s r g hbig
    hcdN hNd
  have hW := item1121N_of h45 h48 h113 h117 h1115 h1120 hK G A c L a R Y d x s r g hbig hcdN hNd
  obtain ⟨j, hj2, hjP, hjx, hjs⟩ := Inverter1118Proof.exists_inverter h45 h113 h117 h1115 hbig
    hcdN hNd hrs hW (step1118S_holds h45 h113 h117 G A c L a R Y d x s r g hbig hcdN hNd hrs hW)
  have hjc := Inverter1118Proof.inverts_of_mem_zpowers hjs h.c_mem_zpowers_s
  have hjd := Inverter1118Proof.inverts_of_mem_zpowers hjx (Item1115Proof.d_mem_zpowers_x h)
  have hjH : j ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [hjc]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)
  have hjL := h.toSec11Std.normalizer_le_normalizer_L h45 hjH
  have hjR : j ∈ Subgroup.normalizer (R : Set G) := by
    have h1 := Subgroup.inf_normalizer_le_normalizer_inf ⟨hjP, Subgroup.le_normalizer hjL⟩
    rwa [h.inf_normalizer_L h45 h113] at h1
  have hgP := Item1119Proof.g_mem_P R g
  set y := g⁻¹ * (j * g * j⁻¹) with hy
  have hyP : y ∈ sec11P R g :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hgP) ((Subgroup.mem_normalizer_iff.mp hjP g).mp hgP)
  have hyc : y * c * y⁻¹ = c := by
    set u := g * c * g⁻¹ * c⁻¹ with hu
    have huD : u ∈ Subgroup.zpowers d := Item1119Proof.conj_c_mul_inv_mem h113 h117 h hgP
    have hju : j * u * j⁻¹ = u⁻¹ := Inverter1118Proof.inverts_of_mem_zpowers hjd huD
    have hcP : c ∈ sec11P R g :=
      Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 h.mem_A)
    have huc : u * c = c * u := (Item1119Proof.commute_of_mem_zpowers_d h113 h117 h huD hcP).symm
    have hgc : g * c * g⁻¹ = u * c := by rw [hu]; group
    have hjc' : j⁻¹ * c * j = c⁻¹ := by
      have e : c = j⁻¹ * c⁻¹ * j := by rw [← hjc]; group
      calc j⁻¹ * c * j = (j⁻¹ * c⁻¹ * j)⁻¹ := by group
        _ = c⁻¹ := by rw [← e]
    have hjgc : (j * g * j⁻¹) * c * (j * g * j⁻¹)⁻¹ = g * c * g⁻¹ := by
      calc (j * g * j⁻¹) * c * (j * g * j⁻¹)⁻¹ = j * (g * (j⁻¹ * c * j) * g⁻¹) * j⁻¹ := by
            group
        _ = j * (g * c * g⁻¹)⁻¹ * j⁻¹ := by rw [hjc']; group
        _ = j * (u * c)⁻¹ * j⁻¹ := by rw [hgc]
        _ = (j * c * j⁻¹)⁻¹ * (j * u * j⁻¹)⁻¹ := by group
        _ = c * u := by rw [hjc, hju, inv_inv, inv_inv]
        _ = g * c * g⁻¹ := by rw [← huc, hgc]
    calc y * c * y⁻¹ = g⁻¹ * ((j * g * j⁻¹) * c * (j * g * j⁻¹)⁻¹) * g := by rw [hy]; group
      _ = c := by rw [hjgc]; group
  have hyR : y ∈ R := by
    rw [← h.inf_normalizer_L h45 h113]
    refine ⟨hyP, h.toSec11Std.normalizer_le_normalizer_L h45 ?_⟩
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [hyc]
    exact Subgroup.mem_zpowers c
  obtain ⟨z, hzR, hz⟩ :=
    Item1118StepsProof.exists_mul_commute_of_conj_mem h.isSylowOf.isPGroup hj2 hjR hyR
  have hPR : sec11P R g ≤ Subgroup.normalizer (R : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr h.g_mem_normalizer)
  have hg'R : g * z ∈ Subgroup.normalizer (R : Set G) :=
    hPR (Subgroup.mul_mem _ hgP (Item1119Proof.R_le_P R g hzR))
  have hg'V := mem_normalizer_V_of_commute h45 h hrs hjL hjR hjx hjs hg'R hz
  have hRV : R ≤ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) :=
    h.R_le_normalizer_V h45
  have hgV : g ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) := by
    have e : g = (g * z) * z⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hg'V (Subgroup.inv_mem _ (hRV hzR))
  have haR : a ∈ R := by
    rw [(h.of_closure_eq hrs).R_eq]
    exact Subgroup.subset_closure (by simp)
  have hag : a * g = g * a :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)).symm
  exact rank3II_11_15_of (h.of_closure_eq hrs) hag h.commute_s_x hRV hgV
    (h.normalizer_P_le_normalizer_V h45 h113) (h.commutator_mem_V h45 h113 outAbelian1016 haR)
    h.a_not_mem_V hcdN hNd (h.htrans hcdN hNd)

end Data

end Item1117Res4Proof

section Main

theorem sec11BigNever_of_res4 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113)
    (h117 : Item117) (h1119 : Item1119) (h1120 : Item1120) (hK : KFact1121Lists) :
    Sec11BigNever := by
  intro G _ _ A c L a R Y d x s r g hbig
  obtain ⟨c₁, L₁, a₁, R₁, Y₁, x₁, s₁, r₁, g₁, hbig₁, hcdN⟩ :=
    h1119 G A c L a R Y d x s r g hbig
  have hNd := hbig₁.toSec11Data.normalizer_sec11P_le_normalizer_zpowers_d h113 h117 hcdN
  exact Item1117Res4Proof.false_of_normalized h45 h48 h113 h117 h1120 hK hbig₁ hcdN hNd

theorem inverter1118_of_res4 (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h113 : Item113)
    (h117 : Item117) (h1119 : Item1119) (h1120 : Item1120) (hK : KFact1121Lists) :
    Inverter1118 :=
  fun G _ _ A c L a R Y d x s r g hbig =>
    (sec11BigNever_of_res4 h45 h48 h113 h117 h1119 h1120 hK G A c L a R Y d x s r g hbig).elim

end Main

end CFSG.RankThree.PartTwo.Sec11
