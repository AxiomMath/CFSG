module

public import CFSG.Milestones.ASVolI.C135.NC

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4 (le_normalizer_c134Q c134Q_le mem_normalizer_centralizer_of_mem
  dact mem_pCoreOf_iff')
open CFSG.Quasithin.H13.Ch4.C135 (cnj coe_cnj slNat slNat_surjective dualHom coe_dualHom
  dualHom_dualHom moduleAct_true_eq le_normalizer_centerOf commutator_mem_Q)
open scoped Matrix commutatorElement Pointwise

variable {G : Type} [Group G]

theorem burnsideC135_comm_of_commute {a b w w' : G} (h1 : Commute w a) (h2 : Commute w b)
    (h3 : Commute w' a) (h4 : Commute w' b) (h5 : Commute w w') :
    (w * a) * (w' * b) * (w * a)⁻¹ * (w' * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hc : Commute w (a * b * a⁻¹) := (h1.mul_right h2).mul_right h1.inv_right
  have hc' : Commute w' (a * b * a⁻¹ * b⁻¹) :=
    ((h3.mul_right h4).mul_right h3.inv_right).mul_right h4.inv_right
  calc (w * a) * (w' * b) * (w * a)⁻¹ * (w' * b)⁻¹
      = w * (a * w') * b * a⁻¹ * w⁻¹ * b⁻¹ * w'⁻¹ := by group
    _ = w * (w' * a) * b * a⁻¹ * w⁻¹ * b⁻¹ * w'⁻¹ := by rw [h3.eq]
    _ = w * w' * ((a * b * a⁻¹) * w⁻¹) * b⁻¹ * w'⁻¹ := by group
    _ = w * w' * (w⁻¹ * (a * b * a⁻¹)) * b⁻¹ * w'⁻¹ := by rw [hc.inv_left.eq]
    _ = (w * w' * w⁻¹) * (a * b * a⁻¹ * b⁻¹) * w'⁻¹ := by group
    _ = w' * (a * b * a⁻¹ * b⁻¹) * w'⁻¹ := by rw [h5.eq, mul_inv_cancel_right]
    _ = (a * b * a⁻¹ * b⁻¹) * w' * w'⁻¹ := by rw [hc'.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem burnsideC135_sq_of_commute {a w : G} (h : Commute w a) (hw : w * w = 1) :
    (w * a) * (w * a) = a * a := by
  calc (w * a) * (w * a) = w * (a * w) * a := by group
    _ = w * (w * a) * a := by rw [h.eq]
    _ = (w * w) * (a * a) := by group
    _ = a * a := by rw [hw, one_mul]

theorem burnsideC135_mem_normalizer_inf {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_inf] at hA hB ⊢
  exact and_congr (hA x) (hB x)

variable [Finite G]

namespace burnsideC135_H1

variable {X R L : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)} {β : ↥(c134Q X L) →* Multiplicative (Fin 2 → Fin 3 → F)}
  {βU : ↥(centerOf (c134Q X L)) →* Multiplicative (Fin 3 → F)}
  (H : burnsideC135_H1 X R L α β βU)
include H

theorem normV : X ≤ Subgroup.normalizer
    ((pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) : Subgroup G) : Set G) :=
  fun _ hx => burnsideC135_mem_normalizer_inf (le_normalizer_pCoreOf 2 X hx)
    (mem_normalizer_centralizer_of_mem (H.normW hx))

theorem W₁_le_V : burnsideC135_Wc β 1 ≤
    pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) := by
  obtain ⟨hsq₁, -⟩ := burnsideC135_W_sq H.dsg
  exact fun w hw => ⟨H.Q_le (burnsideC135_Wc_le 1 hw),
    Subgroup.mem_centralizer_iff.mpr fun w' hw' => burnsideC135_comm_of_sq hsq₁ hw' hw⟩

theorem mem_W₁_of_commute {q : G} (hq : q ∈ c134Q X L)
    (hqc : q ∈ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)) : q ∈ burnsideC135_Wc β 1 := by
  classical
  obtain ⟨hsq₁, -⟩ := burnsideC135_W_sq H.dsg
  refine H.mem_W₁_iff.mpr ⟨hq, ?_⟩
  set y := burnsideC135_qc β q 1 with hy
  obtain ⟨q₂, hq₂0, hq₂1⟩ := H.exists_coords 0 y
  have hq₂Q : ((q₂ : ↥(c134Q X L)) : G) ∈ c134Q X L := q₂.2
  have hq₂W : ((q₂ : ↥(c134Q X L)) : G) ∈ burnsideC135_Wc β 0 :=
    H.mem_W₂_iff.mpr ⟨hq₂Q, by rw [burnsideC135_qc_of_mem hq₂Q]; exact hq₂0⟩
  have hq₂c : burnsideC135_qc β q₂ 1 = y := by rw [burnsideC135_qc_of_mem hq₂Q]; exact hq₂1
  set q₁ := q * ((q₂ : ↥(c134Q X L)) : G)⁻¹ with hq₁def
  have hq₁Q : q₁ ∈ c134Q X L := (c134Q X L).mul_mem hq ((c134Q X L).inv_mem hq₂Q)
  have hq₁W : q₁ ∈ burnsideC135_Wc β 1 := by
    refine H.mem_W₁_iff.mpr ⟨hq₁Q, ?_⟩
    rw [burnsideC135_qc_mul hq ((c134Q X L).inv_mem hq₂Q), burnsideC135_qc_inv hq₂Q]
    simp [hq₂c, hy]
  have hq12 : q = q₁ * q₂ := by rw [hq₁def]; group
  have hcross : ∀ x : Fin 3 → F, x ⨯₃ y = 0 := by
    intro x
    obtain ⟨w, hw0, hw1⟩ := H.exists_coords x 0
    have hwQ : ((w : ↥(c134Q X L)) : G) ∈ c134Q X L := w.2
    have hwW : ((w : ↥(c134Q X L)) : G) ∈ burnsideC135_Wc β 1 :=
      H.mem_W₁_iff.mpr ⟨hwQ, by rw [burnsideC135_qc_of_mem hwQ]; exact hw1⟩
    have hwc : burnsideC135_qc β w 0 = x := by rw [burnsideC135_qc_of_mem hwQ]; exact hw0
    have hU := H.comm _ hwQ _ hq₂Q
    have h1 : ((w : ↥(c134Q X L)) : G) * q₂ * ((w : ↥(c134Q X L)) : G)⁻¹ *
        ((q₂ : ↥(c134Q X L)) : G)⁻¹ = 1 := by
      have h2 : ((w : ↥(c134Q X L)) : G) * q * ((w : ↥(c134Q X L)) : G)⁻¹ * q⁻¹ = 1 := by
        rw [Subgroup.mem_centralizer_iff.mp hqc _ hwW]
        group
      rw [hq12, comm_mul_right' (H.U_comm' hU hq₁Q),
        burnsideC135_comm_of_sq hsq₁ hwW hq₁W] at h2
      simpa using h2
    have h2 := H.uc_comm hwW hq₂W
    rw [h1, hwc, hq₂c] at h2
    rw [← h2]
    have h3 : burnsideC135_uc βU (1 : G) = 0 := by
      rw [burnsideC135_uc_of_mem (centerOf (c134Q X L)).one_mem]
      exact congrArg Multiplicative.toAdd (map_one βU)
    exact h3
  have h0 := hcross (Pi.single 0 1)
  have h1 := hcross (Pi.single 1 1)
  funext i
  fin_cases i
  · have := congrFun h1 2
    simpa [cross_apply] using this
  · have := congrFun h0 2
    simpa [cross_apply] using this
  · have := congrFun h0 1
    simpa [cross_apply] using this

theorem comm_L_mem_W₁ {v l : G} (hv : v ∈ pCoreOf 2 X ⊓
    Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)) (hl : l ∈ L) :
    l * v * l⁻¹ * v⁻¹ ∈ burnsideC135_Wc β 1 := by
  have hvT : v⁻¹ ∈ pCoreOf 2 X := (pCoreOf 2 X).inv_mem hv.1
  have hQ : l * v * l⁻¹ * v⁻¹ ∈ c134Q X L := by
    have h := commutator_mem_Q hvT hl
    rw [inv_inv] at h
    have e : l * v * l⁻¹ * v⁻¹ = (v * l * v⁻¹ * l⁻¹)⁻¹ := by group
    rw [e]
    exact (c134Q X L).inv_mem h
  have hV : l * v * l⁻¹ * v⁻¹ ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) :=
    (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (H.normV (H.le hl)) v).mp hv)
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)).inv_mem hv)
  exact H.mem_W₁_of_commute hQ hV.2

theorem isElemAbelian_V : IsElemAbelian 2
    (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)) := by
  obtain ⟨hsq₁, -⟩ := burnsideC135_W_sq H.dsg
  set V := pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) with hVdef
  have hVX : V ≤ X := inf_le_left.trans (pCoreOf_le 2 X)
  have hcomW : ∀ {v w : G}, v ∈ V → w ∈ burnsideC135_Wc β 1 → Commute w v := fun hv hw =>
    Subgroup.mem_centralizer_iff.mp hv.2 _ hw
  have hconj : ∀ {v l : G}, v ∈ V → l ∈ L → l * v * l⁻¹ = (l * v * l⁻¹ * v⁻¹) * v := fun _ _ => by
    group
  have hcomm : ∀ v ∈ V, ∀ v' ∈ V, v * v' * v⁻¹ * v'⁻¹ = 1 := by
    intro v hv v' hv'
    have hmem : v * v' * v⁻¹ * v'⁻¹ ∈ X ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨X.mul_mem (X.mul_mem (X.mul_mem (hVX hv) (hVX hv')) (X.inv_mem (hVX hv)))
        (X.inv_mem (hVX hv')), Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have hw := H.comm_L_mem_W₁ hv hl
      have hw' := H.comm_L_mem_W₁ hv' hl
      have e : l * (v * v' * v⁻¹ * v'⁻¹) * l⁻¹ =
          (l * v * l⁻¹) * (l * v' * l⁻¹) * (l * v * l⁻¹)⁻¹ * (l * v' * l⁻¹)⁻¹ := by group
      have h2 : l * (v * v' * v⁻¹ * v'⁻¹) * l⁻¹ = v * v' * v⁻¹ * v'⁻¹ := by
        rw [e, hconj hv hl, hconj hv' hl]
        exact burnsideC135_comm_of_commute (hcomW hv hw) (hcomW hv' hw) (hcomW hv hw')
          (hcomW hv' hw') (burnsideC135_comm_of_sq hsq₁ hw hw')
      calc l * (v * v' * v⁻¹ * v'⁻¹) = (l * (v * v' * v⁻¹ * v'⁻¹) * l⁻¹) * l := by group
        _ = v * v' * v⁻¹ * v'⁻¹ * l := by rw [h2]
    rw [H.cent] at hmem
    exact Subgroup.mem_bot.mp hmem
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun v hv => ?_⟩
  · have h := hcomm a a.2 b b.2
    show (a : G) * b = b * a
    calc (a : G) * b = ((a : G) * b * (a : G)⁻¹ * (b : G)⁻¹) * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  · have hmem : v * v ∈ X ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨X.mul_mem (hVX hv) (hVX hv), Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
      have hw := H.comm_L_mem_W₁ hv hl
      have h2 : l * (v * v) * l⁻¹ = v * v := by
        have e : l * (v * v) * l⁻¹ = (l * v * l⁻¹) * (l * v * l⁻¹) := by group
        rw [e, hconj hv hl]
        exact burnsideC135_sq_of_commute (hcomW hv hw) (hsq₁ _ hw)
      calc l * (v * v) = (l * (v * v) * l⁻¹) * l := by group
        _ = v * v * l := by rw [h2]
    rw [H.cent] at hmem
    rw [sq]
    exact Subgroup.mem_bot.mp hmem

theorem exists_V_mul {t : G} (ht : t ∈ pCoreOf 2 X) :
    ∃ v ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G),
      ∃ q ∈ c134Q X L, t = v * q := by
  obtain ⟨c, hcW, hc⟩ := H.exists_mul_mem_V ht
  have hcQ : c ∈ c134Q X L := burnsideC135_Wc_le 0 hcW
  refine ⟨t * c, ⟨(pCoreOf 2 X).mul_mem ht (H.Q_le hcQ), hc⟩, c⁻¹, (c134Q X L).inv_mem hcQ, ?_⟩
  group


theorem le_V_of_shear {v : G}
    (hv : v ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)) {μ : F}
    (hμ0 : μ ≠ 0) (hμ : ∀ (q q' : ↥(c134Q X L)), (q' : G) = v * q * v⁻¹ →
      Multiplicative.toAdd (β q') 0 =
          Multiplicative.toAdd (β q) 0 + μ • Multiplicative.toAdd (β q) 1 ∧
        Multiplicative.toAdd (β q') 1 = Multiplicative.toAdd (β q) 1)
    {t : G} (ht : t ∈ pCoreOf 2 X) (htv : t * v = v * t) :
    t ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) := by
  obtain ⟨v', hv', q, hq, rfl⟩ := H.exists_V_mul ht
  have hVab := H.isElemAbelian_V
  have hvv' : v * v' = v' * v :=
    congrArg Subtype.val (hVab.1.is_comm.comm ⟨v, hv⟩ ⟨v', hv'⟩)
  have hqv : v * q * v⁻¹ = q := by
    have h1 : v' * (q * v) = v' * (v * q) := by
      calc v' * (q * v) = v' * q * v := by group
        _ = v * (v' * q) := htv
        _ = (v * v') * q := by group
        _ = v' * (v * q) := by rw [hvv']; group
    have h2 := mul_left_cancel h1
    calc v * q * v⁻¹ = (q * v) * v⁻¹ := by rw [h2]
      _ = q := by group
  have hmem : v * q * v⁻¹ ∈ c134Q X L := by rw [hqv]; exact hq
  obtain ⟨h0, -⟩ := hμ ⟨q, hq⟩ ⟨_, hmem⟩ rfl
  have e : (⟨v * q * v⁻¹, hmem⟩ : ↥(c134Q X L)) = ⟨q, hq⟩ := Subtype.ext hqv
  rw [e] at h0
  have h3 : μ • Multiplicative.toAdd (β ⟨q, hq⟩) 1 = 0 := by
    have := congrArg (fun z => z - Multiplicative.toAdd (β ⟨q, hq⟩) 0) h0
    simpa using this.symm
  have h4 : Multiplicative.toAdd (β ⟨q, hq⟩) 1 = 0 := (smul_eq_zero.mp h3).resolve_left hμ0
  have hqW : q ∈ burnsideC135_Wc β 1 := burnsideC135_mem_Wc.mpr ⟨hq, h4⟩
  exact (pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G)).mul_mem hv'
    (H.W₁_le_V hqW)

theorem exists_mul_mem_E {v : G}
    (hv : v ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G))
    (htriv : ∀ q ∈ c134Q X L, v * q * v⁻¹ * q⁻¹ ∈ centerOf (c134Q X L)) :
    ∃ w ∈ burnsideC135_Wc β 1, v * w ∈ Subgroup.centralizer (c134Q X L : Set G) := by
  classical
  have hvT : v ∈ pCoreOf 2 X := hv.1
  have hW₁Q : burnsideC135_Wc β 1 ≤ c134Q X L := burnsideC135_Wc_le 1
  have hW₂Q : burnsideC135_Wc β 0 ≤ c134Q X L := burnsideC135_Wc_le 0
  obtain ⟨hsq₁, -⟩ := burnsideC135_W_sq H.dsg
  choose s hs0 hs1 using fun y : Fin 3 → F => H.exists_coords 0 y
  have hsQ : ∀ y, ((s y : ↥(c134Q X L)) : G) ∈ c134Q X L := fun y => (s y).2
  have hsc : ∀ y, burnsideC135_qc β (s y) = ![0, y] := by
    intro y
    rw [burnsideC135_qc_of_mem (hsQ y)]
    funext i
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · exact hs0 y
    · exact hs1 y
  have hsW : ∀ y, ((s y : ↥(c134Q X L)) : G) ∈ burnsideC135_Wc β 0 := fun y =>
    H.mem_W₂_iff.mpr ⟨hsQ y, by rw [hsc]; rfl⟩
  have hqcW : ∀ q ∈ burnsideC135_Wc β 0, burnsideC135_qc β q = ![0, burnsideC135_qc β q 1] := by
    intro q hq
    funext i
    rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) i with rfl | rfl
    · exact (H.mem_W₂_iff.mp hq).2
    · rfl
  let D : (Fin 3 → F) → (Fin 3 → F) := fun y =>
    burnsideC135_uc βU (v * s y * v⁻¹ * ((s y : ↥(c134Q X L)) : G)⁻¹)
  have hDw : ∀ q ∈ burnsideC135_Wc β 0,
      burnsideC135_uc βU (v * q * v⁻¹ * q⁻¹) = D (burnsideC135_qc β q 1) := by
    intro q hq
    show _ = burnsideC135_uc βU (v * s _ * v⁻¹ * ((s _ : ↥(c134Q X L)) : G)⁻¹)
    rw [H.comm_eq_of_qc hvT (hW₂Q hq) (hsQ _) (by rw [hsc, hqcW q hq])]
  have hDadd : ∀ y y', D (y + y') = D y + D y' := by
    intro y y'
    have hmul : ((s y : ↥(c134Q X L)) : G) * s y' ∈ burnsideC135_Wc β 0 :=
      (burnsideC135_Wc β 0).mul_mem (hsW y) (hsW y')
    have h1 : burnsideC135_qc β (((s y : ↥(c134Q X L)) : G) * s y') 1 = y + y' := by
      rw [burnsideC135_qc_mul (hsQ y) (hsQ y'), hsc, hsc]
      rfl
    have h2 := hDw _ hmul
    rw [h1] at h2
    rw [← h2, comm_mul_right' (H.U_comm' (htriv _ (hsQ y')) (hsQ y)),
      burnsideC135_uc_mul (htriv _ (hsQ y)) (htriv _ (hsQ y'))]
  have hrel : ∀ γ : Matrix.SpecialLinearGroup (Fin 3) F, ∃ x : Fin 3 → F, ∀ y,
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ D ((γ : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ y) =
        D y + x ⨯₃ y := by
    intro γ
    obtain ⟨l, hl⟩ := slNat_surjective H.surj.1 γ
    have hcQ : v⁻¹ * l * v * (l : G)⁻¹ ∈ c134Q X L := commutator_mem_Q hvT l.2
    set c := v⁻¹ * l * v * (l : G)⁻¹ with hcdef
    have hcW : c ∈ burnsideC135_Wc β 1 := by
      have h := H.comm_L_mem_W₁ hv l.2
      have h' : ((l : G) * v * (l : G)⁻¹ * v⁻¹)⁻¹ ∈ burnsideC135_Wc β 1 :=
        (burnsideC135_Wc β 1).inv_mem h
      have hc' : v⁻¹ * ((l : G) * v * (l : G)⁻¹ * v⁻¹)⁻¹⁻¹ * v ∈ burnsideC135_Wc β 1 := by
        have hvN : v⁻¹ ∈ Subgroup.normalizer (burnsideC135_Wc β 1 : Set G) :=
          H.normW (pCoreOf_le 2 X ((pCoreOf 2 X).inv_mem hvT))
        have := (Subgroup.mem_normalizer_iff.mp hvN _).mp
          ((burnsideC135_Wc β 1).inv_mem h')
        simpa [mul_assoc] using this
      have e : c = v⁻¹ * ((l : G) * v * (l : G)⁻¹ * v⁻¹)⁻¹⁻¹ * v := by rw [hcdef]; group
      rw [e]
      exact hc'
    refine ⟨burnsideC135_qc β c 0, fun y => ?_⟩
    have hlinv : ((l : G))⁻¹ ∈ L := L.inv_mem l.2
    have hq'mem : (l : G)⁻¹ * s y * ((l : G)⁻¹)⁻¹ ∈ burnsideC135_Wc β 0 :=
      (Subgroup.mem_normalizer_iff.mp (H.dsg.norm₂ hlinv) _).mp (hsW y)
    have hq'c : burnsideC135_qc β ((l : G)⁻¹ * s y * ((l : G)⁻¹)⁻¹) 1 =
        (γ : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ y := by
      rw [H.qc_conj hlinv (hsQ y) 1, hsc]
      have e : (⟨((l : G))⁻¹, hlinv⟩ : ↥L) = l⁻¹ := rfl
      rw [e, map_inv, hl, coe_dualHom, inv_inv]
      rfl
    have hUcomm := htriv _ (hW₂Q hq'mem)
    have h1 := hDw _ hq'mem
    rw [hq'c] at h1
    have hconj := H.uc_conj l.2 hUcomm
    rw [show (⟨(l : G), l.2⟩ : ↥L) = l from rfl, hl] at hconj
    rw [← h1, ← hconj]
    have e2 : (l : G) * (v * ((l : G)⁻¹ * s y * ((l : G)⁻¹)⁻¹) * v⁻¹ *
        ((l : G)⁻¹ * s y * ((l : G)⁻¹)⁻¹)⁻¹) * (l : G)⁻¹ =
        (v * c) * s y * (v * c)⁻¹ * ((s y : ↥(c134Q X L)) : G)⁻¹ := by
      rw [hcdef]; group
    have hcqU : c * s y * c⁻¹ * ((s y : ↥(c134Q X L)) : G)⁻¹ ∈ centerOf (c134Q X L) :=
      H.comm c hcQ _ (hsQ y)
    rw [e2, comm_mul_left' (H.T_comm_U hvT hcqU), burnsideC135_uc_mul hcqU (htriv _ (hsQ y)),
      H.uc_comm hcW (hsW y), hsc]
    simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    exact add_comm _ _
  obtain ⟨y₀, hy₀⟩ := burnsideC135_weight H.card D hDadd hrel
  obtain ⟨w₀, hw₀0, hw₀1⟩ := H.exists_coords (-y₀) 0
  have hw₀Q : ((w₀ : ↥(c134Q X L)) : G) ∈ c134Q X L := w₀.2
  have hw₀W : ((w₀ : ↥(c134Q X L)) : G) ∈ burnsideC135_Wc β 1 :=
    H.mem_W₁_iff.mpr ⟨hw₀Q, by rw [burnsideC135_qc_of_mem hw₀Q]; exact hw₀1⟩
  have hw₀c : burnsideC135_qc β w₀ 0 = -y₀ := by rw [burnsideC135_qc_of_mem hw₀Q]; exact hw₀0
  refine ⟨w₀, hw₀W, ?_⟩
  have hW₂ : ∀ q ∈ burnsideC135_Wc β 0, (v * w₀) * q = q * (v * w₀) := by
    intro q hq
    have hqQ := hW₂Q hq
    have hwqU := H.comm _ hw₀Q q hqQ
    have h1 : (v * w₀) * q * (v * w₀)⁻¹ * q⁻¹ = 1 := by
      refine H.eq_one_of_uc ?_ ?_
      · rw [comm_mul_left' (H.T_comm_U hvT hwqU)]
        exact (centerOf (c134Q X L)).mul_mem hwqU (htriv q hqQ)
      · rw [comm_mul_left' (H.T_comm_U hvT hwqU), burnsideC135_uc_mul hwqU (htriv q hqQ),
          H.uc_comm hw₀W hq, hDw q hq, hy₀, hw₀c, LinearMap.map_neg₂, neg_add_cancel]
    calc (v * w₀) * q = ((v * w₀) * q * (v * w₀)⁻¹ * q⁻¹) * (q * (v * w₀)) := by group
      _ = q * (v * w₀) := by rw [h1, one_mul]
  have hW₁ : ∀ q ∈ burnsideC135_Wc β 1, q * (v * w₀) = (v * w₀) * q := by
    intro q hq
    have h1 : q * v = v * q := Subgroup.mem_centralizer_iff.mp hv.2 q hq
    have h2 : q * w₀ = w₀ * q := burnsideC135_comm_of_sq hsq₁ hq hw₀W
    calc q * (v * w₀) = (q * v) * w₀ := by group
      _ = v * (q * w₀) := by rw [h1]; group
      _ = (v * w₀) * q := by rw [h2]; group
  refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
  obtain ⟨q₂, hq₂0, hq₂1⟩ := H.exists_coords 0 (burnsideC135_qc β q 1)
  have hq₂Q : ((q₂ : ↥(c134Q X L)) : G) ∈ c134Q X L := q₂.2
  have hq₂W : ((q₂ : ↥(c134Q X L)) : G) ∈ burnsideC135_Wc β 0 :=
    H.mem_W₂_iff.mpr ⟨hq₂Q, by rw [burnsideC135_qc_of_mem hq₂Q]; exact hq₂0⟩
  have hq₁W : q * ((q₂ : ↥(c134Q X L)) : G)⁻¹ ∈ burnsideC135_Wc β 1 := by
    refine H.mem_W₁_iff.mpr ⟨(c134Q X L).mul_mem hq ((c134Q X L).inv_mem hq₂Q), ?_⟩
    rw [burnsideC135_qc_mul hq ((c134Q X L).inv_mem hq₂Q), burnsideC135_qc_inv hq₂Q,
      burnsideC135_qc_of_mem hq₂Q]
    simp [hq₂1]
  have e : q = (q * ((q₂ : ↥(c134Q X L)) : G)⁻¹) * q₂ := by group
  rw [e, mul_assoc, ← hW₂ _ hq₂W, ← mul_assoc, hW₁ _ hq₁W, mul_assoc]

theorem E_le_V : pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) ≤
    pCoreOf 2 X ⊓ Subgroup.centralizer (burnsideC135_Wc β 1 : Set G) :=
  inf_le_inf_left _ (Subgroup.centralizer_le (burnsideC135_Wc_le 1))

theorem normE : X ≤ Subgroup.normalizer
    ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) : Subgroup G) : Set G) :=
  fun _ hx => burnsideC135_mem_normalizer_inf (le_normalizer_pCoreOf 2 X hx)
    (mem_normalizer_centralizer_of_mem (H.normQ hx))

theorem T_comm_E {t e : G} (ht : t ∈ pCoreOf 2 X)
    (he : e ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) : t * e = e * t := by
  obtain ⟨v, hv, q, hq, rfl⟩ := H.exists_V_mul ht
  have hve : v * e = e * v :=
    congrArg Subtype.val (H.isElemAbelian_V.1.is_comm.comm ⟨v, hv⟩ ⟨e, H.E_le_V he⟩)
  have hqe : q * e = e * q := (Subgroup.mem_centralizer_iff.mp he.2 q hq).symm.symm
  calc v * q * e = v * (q * e) := by group
    _ = v * (e * q) := by rw [hqe]
    _ = (v * e) * q := by group
    _ = e * (v * q) := by rw [hve]; group

theorem comm_L_mem_U {e l : G} (he : e ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G))
    (hl : l ∈ L) : l * e * l⁻¹ * e⁻¹ ∈ centerOf (c134Q X L) := by
  have heT : e⁻¹ ∈ pCoreOf 2 X := (pCoreOf 2 X).inv_mem he.1
  have hQ : l * e * l⁻¹ * e⁻¹ ∈ c134Q X L := by
    have h := commutator_mem_Q heT hl
    rw [inv_inv] at h
    have e' : l * e * l⁻¹ * e⁻¹ = (e * l * e⁻¹ * l⁻¹)⁻¹ := by group
    rw [e']
    exact (c134Q X L).inv_mem h
  have hE : l * e * l⁻¹ * e⁻¹ ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G) :=
    (pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (H.normE (H.le hl)) e).mp he)
      ((pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)).inv_mem he)
  exact ⟨hQ, hE.2⟩

theorem mem_U_of_commute {e l : G}
    (he : e ∈ pCoreOf 2 X ⊓ Subgroup.centralizer (c134Q X L : Set G)) (hl : l ∈ L)
    (hl1 : slNat α ⟨l, hl⟩ ≠ 1) (hl2 : slNat α ⟨l, hl⟩ * slNat α ⟨l, hl⟩ = 1)
    (hle : l * e = e * l) : e ∈ centerOf (c134Q X L) := by
  classical
  have heX : e ∈ X := pCoreOf_le 2 X he.1
  let f : ↥L → Fin 1 → Fin 3 → F := fun g _ =>
    burnsideC135_uc βU ((g : G) * e * (g : G)⁻¹ * e⁻¹)
  have hf : ∀ g h, f (g * h) = f g + dact ((slNat α g : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) (f h) := by
    intro g h
    funext i
    show burnsideC135_uc βU (((g * h : ↥L) : G) * e * ((g * h : ↥L) : G)⁻¹ * e⁻¹) =
      burnsideC135_uc βU ((g : G) * e * (g : G)⁻¹ * e⁻¹) +
        ((slNat α g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
          burnsideC135_uc βU ((h : G) * e * (h : G)⁻¹ * e⁻¹)
    have hU1 := H.comm_L_mem_U he g.2
    have hU2 := H.comm_L_mem_U he h.2
    have hU2' : (g : G) * ((h : G) * e * (h : G)⁻¹ * e⁻¹) * (g : G)⁻¹ ∈ centerOf (c134Q X L) :=
      (Subgroup.mem_normalizer_iff.mp (H.normU (H.le g.2)) _).mp hU2
    have e1 : ((g * h : ↥L) : G) * e * ((g * h : ↥L) : G)⁻¹ * e⁻¹ =
        ((g : G) * ((h : G) * e * (h : G)⁻¹ * e⁻¹) * (g : G)⁻¹) *
          ((g : G) * e * (g : G)⁻¹ * e⁻¹) := by
      simp only [Subgroup.coe_mul]; group
    rw [e1, burnsideC135_uc_mul hU2' hU1, H.uc_conj g.2 hU2, add_comm]
  have hker : ∀ a : ↥L, slNat α a = 1 → f a = 0 := by
    intro a ha
    have h1 : a ∈ (slNat α).ker := ha
    rw [burnsideC135_slNat_ker H.surj] at h1
    have h2 : (a : G) ∈ pCoreOf 2 L := (mem_pCoreOf_iff' a).mpr h1
    have h3 : (a : G) ∈ pCoreOf 2 X := MS93.pCoreOf_le_pCoreOf_of_le_normalizer H.le H.normL h2
    have h4 := H.T_comm_E h3 he
    funext i
    show burnsideC135_uc βU ((a : G) * e * (a : G)⁻¹ * e⁻¹) = 0
    rw [h4, show e * (a : G) * (a : G)⁻¹ * e⁻¹ = 1 by group,
      burnsideC135_uc_of_mem (centerOf (c134Q X L)).one_mem]
    exact congrArg Multiplicative.toAdd (map_one βU)
  have hfl : f ⟨l, hl⟩ = 0 := by
    funext i
    show burnsideC135_uc βU (l * e * l⁻¹ * e⁻¹) = 0
    rw [hle, show e * l * l⁻¹ * e⁻¹ = 1 by group,
      burnsideC135_uc_of_mem (centerOf (c134Q X L)).one_mem]
    exact congrArg Multiplicative.toAdd (map_one βU)
  obtain ⟨m, hm⟩ := burnsideC135_exists_coboundary_two H.card (slNat_surjective H.surj.1) hf
    hker hl1 hl2 hfl
  obtain ⟨u₀, hu₀⟩ := H.dsg.natU_onto (Multiplicative.ofAdd (m 0))
  have hu₀U : (u₀ : G) ∈ centerOf (c134Q X L) := u₀.2
  have hu₀c : burnsideC135_uc βU (u₀ : G) = m 0 := by
    rw [burnsideC135_uc_of_mem hu₀U]
    exact congrArg Multiplicative.toAdd hu₀
  have hcomm : ∀ g ∈ L, g * e * g⁻¹ * e⁻¹ = g * u₀ * g⁻¹ * (u₀ : G)⁻¹ := by
    intro g hg
    have hU1 := H.comm_L_mem_U he hg
    have hgu : g * u₀ * g⁻¹ ∈ centerOf (c134Q X L) :=
      (Subgroup.mem_normalizer_iff.mp (H.normU (H.le hg)) _).mp hu₀U
    have hU2 : g * u₀ * g⁻¹ * (u₀ : G)⁻¹ ∈ centerOf (c134Q X L) :=
      (centerOf (c134Q X L)).mul_mem hgu ((centerOf (c134Q X L)).inv_mem hu₀U)
    have h1 := congrFun (hm ⟨g, hg⟩) 0
    have h2 : burnsideC135_uc βU (g * e * g⁻¹ * e⁻¹) =
        burnsideC135_uc βU (g * u₀ * g⁻¹ * (u₀ : G)⁻¹) := by
      rw [burnsideC135_uc_mul hgu ((centerOf (c134Q X L)).inv_mem hu₀U),
        burnsideC135_uc_inv hu₀U, H.uc_conj hg hu₀U, hu₀c]
      exact h1.trans (sub_eq_add_neg _ _)
    have h3 : (g * e * g⁻¹ * e⁻¹) * (g * u₀ * g⁻¹ * (u₀ : G)⁻¹)⁻¹ = 1 := by
      refine H.eq_one_of_uc ((centerOf (c134Q X L)).mul_mem hU1
        ((centerOf (c134Q X L)).inv_mem hU2)) ?_
      rw [burnsideC135_uc_mul hU1 ((centerOf (c134Q X L)).inv_mem hU2), burnsideC135_uc_inv hU2,
        h2, add_neg_cancel]
    exact mul_inv_eq_one.mp h3
  have hmem : e * (u₀ : G)⁻¹ ∈ X ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨X.mul_mem heX (X.inv_mem (pCoreOf_le 2 X (H.Q_le hu₀U.1))),
      Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    have h1 := hcomm g hg
    set k := g * e * g⁻¹ * e⁻¹ with hk
    have hkU : k ∈ centerOf (c134Q X L) := H.comm_L_mem_U he hg
    have hke : k * e = e * k := Subgroup.mem_centralizer_iff.mp he.2 k hkU.1
    have hku : k * u₀ = u₀ * k := H.U_comm' hkU hu₀U.1 |>.symm
    have hge : g * e = k * e * g := by rw [hk]; group
    have hgu : g * u₀ = k * u₀ * g := by rw [h1]; group
    calc g * (e * (u₀ : G)⁻¹) = (g * e) * (u₀ : G)⁻¹ := by group
      _ = k * e * g * (u₀ : G)⁻¹ := by rw [hge]
      _ = k * e * (g * (u₀ : G)⁻¹) := by group
      _ = k * e * ((u₀ : G)⁻¹ * k⁻¹ * g) := by
          congr 1
          have : g * (u₀ : G)⁻¹ = (u₀ : G)⁻¹ * k⁻¹ * (k * u₀ * g) * (u₀ : G)⁻¹ * g⁻¹ * g *
              (u₀ : G)⁻¹ * u₀ := by group
          rw [← hgu] at this
          calc g * (u₀ : G)⁻¹ = (u₀ : G)⁻¹ * k⁻¹ * (g * u₀) * (u₀ : G)⁻¹ := by
                rw [hgu]; group
            _ = (u₀ : G)⁻¹ * k⁻¹ * g := by group
      _ = (k * e * (u₀ : G)⁻¹ * k⁻¹) * g := by group
      _ = (e * (u₀ : G)⁻¹) * g := by
          congr 1
          calc k * e * (u₀ : G)⁻¹ * k⁻¹ = e * (k * (u₀ : G)⁻¹) * k⁻¹ := by rw [hke]; group
            _ = e * ((u₀ : G)⁻¹ * k) * k⁻¹ := by
                congr 2
                calc k * (u₀ : G)⁻¹ = (u₀ : G)⁻¹ * (u₀ * k) * (u₀ : G)⁻¹ := by group
                  _ = (u₀ : G)⁻¹ * (k * u₀) * (u₀ : G)⁻¹ := by rw [hku]
                  _ = (u₀ : G)⁻¹ * k := by group
            _ = e * (u₀ : G)⁻¹ := by group
  rw [H.cent, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  rw [hmem]
  exact hu₀U


theorem uc_inj {a b : G} (ha : a ∈ centerOf (c134Q X L)) (hb : b ∈ centerOf (c134Q X L))
    (h : burnsideC135_uc βU a = burnsideC135_uc βU b) : a = b := by
  have h1 : a * b⁻¹ = 1 := by
    refine H.eq_one_of_uc ((centerOf (c134Q X L)).mul_mem ha ((centerOf (c134Q X L)).inv_mem hb)) ?_
    rw [burnsideC135_uc_mul ha ((centerOf (c134Q X L)).inv_mem hb), burnsideC135_uc_inv hb, h,
      add_neg_cancel]
  exact mul_inv_eq_one.mp h1

theorem uc_one : burnsideC135_uc βU (1 : G) = 0 := by
  rw [burnsideC135_uc_of_mem (centerOf (c134Q X L)).one_mem]
  exact congrArg Multiplicative.toAdd (map_one βU)

theorem mem_mul {x : G} (hx : x ∈ X) : ∃ l ∈ L, ∃ t ∈ pCoreOf 2 X, x = l * t := by
  classical
  have hxU : x ∈ Subgroup.normalizer (centerOf (c134Q X L) : Set G) := H.normU hx
  choose s hs using fun v : Fin 3 → F => H.dsg.natU_onto (Multiplicative.ofAdd v)
  have hsU : ∀ v, ((s v : ↥(centerOf (c134Q X L))) : G) ∈ centerOf (c134Q X L) := fun v =>
    (s v).2
  have hsc : ∀ v, burnsideC135_uc βU (s v : G) = v := fun v => by
    rw [burnsideC135_uc_of_mem (hsU v), hs v]
    rfl
  have hxsU : ∀ v, x * s v * x⁻¹ ∈ centerOf (c134Q X L) := fun v =>
    (Subgroup.mem_normalizer_iff.mp hxU _).mp (hsU v)
  let φ : (Fin 3 → F) → (Fin 3 → F) := fun v => burnsideC135_uc βU (x * s v * x⁻¹)
  have hs_uc : ∀ u ∈ centerOf (c134Q X L), ((s (burnsideC135_uc βU u)) : G) = u := fun u hu =>
    H.uc_inj (hsU _) hu (hsc _)
  have hφadd : ∀ v w, φ (v + w) = φ v + φ w := by
    intro v w
    have e : ((s (v + w)) : G) = s v * s w := by
      refine H.uc_inj (hsU _) ((centerOf (c134Q X L)).mul_mem (hsU v) (hsU w)) ?_
      rw [burnsideC135_uc_mul (hsU v) (hsU w), hsc, hsc, hsc]
    show burnsideC135_uc βU (x * s (v + w) * x⁻¹) =
      burnsideC135_uc βU (x * s v * x⁻¹) + burnsideC135_uc βU (x * s w * x⁻¹)
    rw [e, show x * (((s v) : G) * s w) * x⁻¹ = (x * s v * x⁻¹) * (x * s w * x⁻¹) by group,
      burnsideC135_uc_mul (hxsU v) (hxsU w)]
  have hφ0 : φ 0 = 0 := by
    have := hφadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hφsmul : ∀ (c : F) v, φ (c • v) = c • φ v := by
    intro c v
    rcases H.eq_zero_or_one c with rfl | rfl
    · rw [zero_smul, zero_smul, hφ0]
    · rw [one_smul, one_smul]
  let M : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => φ (Pi.single j 1) i
  have hM : ∀ v, φ v = M *ᵥ v := by
    intro v
    conv_lhs => rw [burnsideC135_vec_eq v]
    rw [hφadd, hφadd, hφsmul, hφsmul, hφsmul]
    funext i
    simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]
  have hdet : M.det = 1 := by
    rcases H.eq_zero_or_one M.det with h | h
    · exfalso
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
      have h1 : φ v = 0 := by rw [hM, hv]
      have h2 : x * s v * x⁻¹ = 1 := H.eq_one_of_uc (hxsU v) h1
      have h3 : ((s v) : G) = 1 := by
        have := congrArg (fun g => x⁻¹ * g * x) h2
        simpa [mul_assoc] using this
      apply hv0
      rw [← hsc v, h3, H.uc_one]
    · exact h
  set γ₀ : Matrix.SpecialLinearGroup (Fin 3) F := ⟨M, hdet⟩ with hγ₀
  obtain ⟨l, hl⟩ := slNat_surjective H.surj.1 γ₀
  refine ⟨l, l.2, (l : G)⁻¹ * x, H.centralizer_U_le ⟨X.mul_mem (X.inv_mem (H.le l.2)) hx, ?_⟩,
    by group⟩
  show (l : G)⁻¹ * x ∈ Subgroup.centralizer (centerOf (c134Q X L) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hlinv : ((l : G))⁻¹ ∈ L := L.inv_mem l.2
  have hxu : x * u * x⁻¹ ∈ centerOf (c134Q X L) := (Subgroup.mem_normalizer_iff.mp hxU _).mp hu
  have hmem : (l : G)⁻¹ * (x * u * x⁻¹) * ((l : G)⁻¹)⁻¹ ∈ centerOf (c134Q X L) :=
    (Subgroup.mem_normalizer_iff.mp (H.normU (H.le hlinv)) _).mp hxu
  have h1 : (l : G)⁻¹ * (x * u * x⁻¹) * ((l : G)⁻¹)⁻¹ = u := by
    refine H.uc_inj hmem hu ?_
    rw [H.uc_conj hlinv hxu]
    have e : (⟨((l : G))⁻¹, hlinv⟩ : ↥L) = l⁻¹ := rfl
    have e2 : burnsideC135_uc βU (x * u * x⁻¹) = M *ᵥ burnsideC135_uc βU u := by
      rw [← hM]
      show _ = burnsideC135_uc βU (x * s _ * x⁻¹)
      rw [hs_uc u hu]
    rw [e, map_inv, hl, e2, Matrix.mulVec_mulVec]
    have e3 : (((γ₀⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M) =
        1 := by
      have := congrArg Subtype.val (inv_mul_cancel γ₀)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
      exact this
    rw [e3, Matrix.one_mulVec]
  calc u * ((l : G)⁻¹ * x) =
        ((l : G)⁻¹ * (x * u * x⁻¹) * ((l : G)⁻¹)⁻¹) * ((l : G)⁻¹ * x) := by rw [h1]
    _ = ((l : G)⁻¹ * x) * u := by group

end burnsideC135_H1

end CFSG.ASVolI

end
