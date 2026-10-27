module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXTrans
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
import CFSG.LocalAnalysis.StandardType.GGQTwoDSlFix
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXPairA
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrFixAlg

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem ggQTwoDUnit_X_pair (hL1 : GGQTwoL1Input) (hEA : GGQTwoEdgeAmbientInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b') :
    ∀ r ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r ∈ ggCoxRefl M e →
      ∀ r' ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r' ∈ ggCoxRefl M e → r * r' ≠ r' * r →
        Nat.card ↥(ggRankOneIn (qtwoDelX ψ c g) Bs r) = 6 →
          UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (ggRankTwoIn (qtwoDelX ψ c g) Bs r r')
            (ggRankOneIn (qtwoDelX ψ c g) Bs r) (ggRankOneIn (qtwoDelX ψ c g) Bs r') := by
  intro r hrA hrC r' hr'A hr'C hnc _h6
  classical
  obtain ⟨p₀, p₁, p₂, n, a₀, hp1, hp2, hc0, hc1, hc2, hnN, hnact, heq1, heq2⟩ :=
    qtwoDB21_normal_form_pair hbase hcoords hdel hm hrA hrC hr'A hr'C hnc
  have hp0p1 : p₀ ≠ p₁ := fun h => by have := congrArg Fin.val h; omega
  have hp1p2 : p₁ ≠ p₂ := fun h => by have := congrArg Fin.val h; omega
  have hp0p2 : p₀ ≠ p₂ := fun h => by have := congrArg Fin.val h; omega
  set e₁ : MulAut ↥Bs := (((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    with he₁
  set e₂ : MulAut ↥Bs := (((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    with he₂
  have heA₁ : e₁ ∈ ggAutomizer L Bs := by
    rw [he₁]; exact (ε (Equiv.swap p₀ p₁)).2
  have heA₂ : e₂ ∈ ggAutomizer L Bs := by
    rw [he₂]; exact (ε (Equiv.swap p₁ p₂)).2
  have heC₁ : e₁ ∈ ggCoxRefl M e := by
    rw [he₁]
    exact hcoords.cox false p₀ p₁ hp0p1
      (((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
      (Subgroup.mem_sup_left (ε (Equiv.swap p₀ p₁)).2) (fun s => by
        rw [hcoords.perm]; simp [dTau])
  have heC₂ : e₂ ∈ ggCoxRefl M e := by
    rw [he₂]
    exact hcoords.cox false p₁ p₂ hp1p2
      (((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
      (Subgroup.mem_sup_left (ε (Equiv.swap p₁ p₂)).2) (fun s => by
        rw [hcoords.perm]; simp [dTau])
  have henc : e₁ * e₂ ≠ e₂ * e₁ := by
    intro h
    apply hnc
    have hr1 : a₀⁻¹ * e₁ * a₀ = r := by rw [← heq1]; group
    have hr2 : a₀⁻¹ * e₂ * a₀ = r' := by rw [← heq2]; group
    calc r * r' = (a₀⁻¹ * e₁ * a₀) * (a₀⁻¹ * e₂ * a₀) := by rw [hr1, hr2]
      _ = a₀⁻¹ * (e₁ * e₂) * a₀ := by group
      _ = a₀⁻¹ * (e₂ * e₁) * a₀ := by rw [h]
      _ = (a₀⁻¹ * e₂ * a₀) * (a₀⁻¹ * e₁ * a₀) := by group
      _ = r' * r := by rw [hr1, hr2]
  have hEA_L : ggRankTwo Bs e₁ e₂ = ggRankTwoIn L Bs e₁ e₂ :=
    hEA G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM L (Or.inl rfl) e₁ heA₁ heC₁ e₂ heA₂ heC₂ henc
  have hrank : ggRankTwoIn L Bs e₁ e₂ =
      (coordBlockSU F0 2 1 ({p₀, p₁, p₂} : Finset (Fin m))).map ψ := by
    rw [← hbase.range]
    exact ggQTwoDUnit_rankTwoIn_eq (K := F0) hbase.hyp hbase.card_field hbase.diag
      hp0p1 hp1p2 hp0p2
      (fun s => by rw [he₁]; simpa only [Equiv.swap_inv] using hbase.perm (Equiv.swap p₀ p₁) s)
      (fun s => by rw [he₂]; simpa only [Equiv.swap_inv] using hbase.perm (Equiv.swap p₁ p₂) s)
  have hRU : (ggRankOne Bs r).map (MulAut.conj n).toMonoidHom =
      (ggSuPairBlock F0 2 1 m p₀ p₁).map ψ := by
    rw [ggRankOne_map_conj hnact r, heq1]
    rw [(hL1 G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM L (Or.inl rfl) e₁ heA₁ heC₁).1]
    rw [he₁, hbase.rankOne p₀ p₁ hp0p1]
  have hRU' : (ggRankOne Bs r').map (MulAut.conj n).toMonoidHom =
      (ggSuPairBlock F0 2 1 m p₁ p₂).map ψ := by
    rw [ggRankOne_map_conj hnact r', heq2]
    rw [(hL1 G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM L (Or.inl rfl) e₂ heA₂ heC₂).1]
    rw [he₂, hbase.rankOne p₁ p₂ hp1p2]
  have hRW : (ggRankTwo Bs r r').map (MulAut.conj n).toMonoidHom =
      (coordBlockSU F0 2 1 ({p₀, p₁, p₂} : Finset (Fin m))).map ψ := by
    rw [ggRankTwo_map_conj hnact r r', heq1, heq2, hEA_L, hrank]
  have hW0 : UnitaryBlockStandardPair F0 2 1 (ggRankTwo Bs r r') (ggRankOne Bs r)
      (ggRankOne Bs r') := by
    have hchart := ggQTwoDUnit_stdPair (K := F0) (f := 1) (n := m) ψ hbase.hyp.ker
      (by omega : 3 ≤ m) hp0p1 hp1p2 hp0p2
    refine UnitaryBlockStandardPair.of_map_conj n ?_
    rw [hRW, hRU, hRU']
    exact hchart
  have hGalois : UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (ggRankTwo Bs r r')
      (ggRankOne Bs r) (ggRankOne Bs r') := by
    letI : Fintype F0 := Fintype.ofFinite F0
    letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    exact ggPhanNSAPairAux_stdPair_congr_field (K := F0) (K' := GaloisField 2 2)
      (FiniteField.ringEquivOfCardEq (K := GaloisField 2 2) (K' := F0) (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          natCard_galoisField_two_two, hbase.card_field])) hW0
  rw [← ggQTwoDUnit_X_rankTwo hEA hcfg hm hM hbase hcoords hdel r hrA hrC r' hr'A hr'C hnc,
    ← ggQTwoDUnit_X_rankOne hL1 hcfg hm hM hbase hcoords hdel r hrA hrC,
    ← ggQTwoDUnit_X_rankOne hL1 hcfg hm hM hbase hcoords hdel r' hr'A hr'C]
  exact hGalois

private lemma qtwoDB21_ofMul_toMul {α : Type*} [Mul α] (s : Additive α) :
    Additive.ofMul (Additive.toMul s) = s := rfl

private noncomputable def qtwoDB21_lin (βL : Additive ↥Bs ≃+ DVec m) :
    MulAut ↥Bs →* (DVec m ≃ₗ[ZMod 3] DVec m) :=
  @CFSG.StandardType.ggLin 3 Nat.fact_prime_three ↥Bs inferInstance (DVec m) inferInstance
    (inferInstance : Module (ZMod 3) (DVec m)) βL

private lemma qtwoDB21_lin_apply (βL : Additive ↥Bs ≃+ DVec m) (r : MulAut ↥Bs) (s : ↥Bs) :
    qtwoDB21_lin βL r (βL (Additive.ofMul s)) = βL (Additive.ofMul (r s)) :=
  @CFSG.StandardType.ggLin_apply_ofMul 3 Nat.fact_prime_three ↥Bs inferInstance (DVec m)
    inferInstance (inferInstance : Module (ZMod 3) (DVec m)) βL r s

private lemma qtwoDB21_lin_injective (βL : Additive ↥Bs ≃+ DVec m) :
    Function.Injective (qtwoDB21_lin βL) := by
  intro r r' h
  refine MulEquiv.ext fun s => Additive.ofMul.injective (βL.injective ?_)
  have h' := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T (βL (Additive.ofMul s))) h
  rwa [qtwoDB21_lin_apply, qtwoDB21_lin_apply] at h'

private lemma qtwoDB21_lin_conj (a r : MulAut ↥Bs) :
    qtwoDB21_lin βL (a * r * a⁻¹) =
      qtwoDB21_lin βL a * qtwoDB21_lin βL r * (qtwoDB21_lin βL a)⁻¹ := by
  simp only [map_mul, map_inv]

private lemma qtwoDB21_conj_comm {a r r' : MulAut ↥Bs} (h : r * r' = r' * r) :
    (a * r * a⁻¹) * (a * r' * a⁻¹) = (a * r' * a⁻¹) * (a * r * a⁻¹) := by
  rw [show (a * r * a⁻¹) * (a * r' * a⁻¹) = a * (r * r') * a⁻¹ by group,
    show (a * r' * a⁻¹) * (a * r * a⁻¹) = a * (r' * r) * a⁻¹ by group, h]

private lemma qtwoDB21_lin_conj_comm {a r r' : MulAut ↥Bs} (h : r * r' = r' * r) :
    qtwoDB21_lin βL (a * r * a⁻¹) * qtwoDB21_lin βL (a * r' * a⁻¹) =
      qtwoDB21_lin βL (a * r' * a⁻¹) * qtwoDB21_lin βL (a * r * a⁻¹) := by
  have h' := congrArg (qtwoDB21_lin βL) (qtwoDB21_conj_comm (a := a) h)
  rw [map_mul (qtwoDB21_lin βL) (a * r * a⁻¹) (a * r' * a⁻¹),
    map_mul (qtwoDB21_lin βL) (a * r' * a⁻¹) (a * r * a⁻¹)] at h'
  exact h'

private lemma qtwoDB21_conj_ne {a r r' : MulAut ↥Bs} (h : r * r' ≠ r' * r) :
    (a * r * a⁻¹) * (a * r' * a⁻¹) ≠ (a * r' * a⁻¹) * (a * r * a⁻¹) := by
  intro hh
  apply h
  have h' := congrArg (fun w => a⁻¹ * w * a) hh
  rwa [show a⁻¹ * ((a * r * a⁻¹) * (a * r' * a⁻¹)) * a = r * r' by group,
    show a⁻¹ * ((a * r' * a⁻¹) * (a * r * a⁻¹)) * a = r' * r by group] at h'

private lemma qtwoDB21_lin_of_action {r : MulAut ↥Bs} {W : DVec m ≃ₗ[ZMod 3] DVec m}
    (h : ∀ s : ↥Bs, βL (Additive.ofMul (r s)) = W (βL (Additive.ofMul s))) :
    qtwoDB21_lin βL r = W := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨s, rfl⟩ := βL.surjective v
  rw [← qtwoDB21_ofMul_toMul s, qtwoDB21_lin_apply, h]

private lemma qtwoDB21_perm_of_lin (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    {r : MulAut ↥Bs} {u v : Fin m} (hr : qtwoDB21_lin βL r = dTau m false u v) :
    r = ((ε (Equiv.swap u v) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
  apply qtwoDB21_lin_injective βL
  rw [hr, qtwoDB21_lin_of_action (fun s => hcoords.perm (Equiv.swap u v) s),
    qtwoDB21_dTau_false]

private lemma qtwoDB21_cox_of_perm (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    {u v : Fin m} (huv : u ≠ v) :
    ((ε (Equiv.swap u v) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∈ ggCoxRefl M e :=
  hcoords.cox false u v huv _ (Subgroup.mem_sup_left (ε (Equiv.swap u v)).2) (fun s => by
    rw [hcoords.perm]; simp [dTau])

private lemma qtwoDB21_w₀_conj (D V T : DVec m ≃ₗ[ZMod 3] DVec m) :
    (D * V) * T * (D * V)⁻¹ = D * (V * T * V⁻¹) * D⁻¹ := by group

private lemma qtwoDB21_dSign_comm_dTau_false {u v w₁ w₂ : Fin m}
    (h1 : w₁ ≠ u) (h2 : w₁ ≠ v) (h3 : w₂ ≠ u) (h4 : w₂ ≠ v) :
    dSign m u v * dTau m false w₁ w₂ * (dSign m u v)⁻¹ = dTau m false w₁ w₂ := by
  rw [qtwoDB21_dTau_false m w₁ w₂,
    qtwoDB21_dSign_comm_dPerm (Equiv.swap_apply_of_ne_of_ne h1.symm h3.symm)
      (Equiv.swap_apply_of_ne_of_ne h2.symm h4.symm)]
  group

private lemma qtwoDB21_rankTwo_le (hEA : GGQTwoEdgeAmbientInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase p B Bs x L ψ ε)
    {r r' : MulAut ↥Bs} {u v w : Fin m} (huv : u ≠ v) (hvw : v ≠ w) (huw : u ≠ w)
    (hrL : r ∈ ggAutomizer L Bs) (hrC : r ∈ ggCoxRefl M e)
    (hr'L : r' ∈ ggAutomizer L Bs) (hr'C : r' ∈ ggCoxRefl M e)
    (hr : r = ((ε (Equiv.swap u v) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (hr' : r' = ((ε (Equiv.swap v w) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (hne : r * r' ≠ r' * r) :
    ggRankTwo Bs r r' ≤ (coordBlockSU F0 2 1 ({u, v, w} : Finset (Fin m))).map ψ := by
  rw [hEA G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM L (Or.inl rfl) r hrL hrC r' hr'L hr'C hne]
  have hle := ggQTwoDUnit_rankTwoIn_le (K := F0) (f := 1) (n := m) (a := u) (b := v) (c := w)
    hbase.hyp hbase.diag huv hvw huw (r := r) (r' := r')
    (fun s => by rw [hr]; simpa only [Equiv.swap_inv] using hbase.perm (Equiv.swap u v) s)
    (fun s => by rw [hr']; simpa only [Equiv.swap_inv] using hbase.perm (Equiv.swap v w) s)
  rwa [hbase.range] at hle

private lemma qtwoDB21_pair_lin (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') (hm : 7 ≤ m)
    {r r' : MulAut ↥Bs} (hrA : r ∈ ggAutomizer (qtwoDelX ψ c g) Bs)
    (hrC : r ∈ ggCoxRefl M e) (hr'A : r' ∈ ggAutomizer (qtwoDelX ψ c g) Bs)
    (hr'C : r' ∈ ggCoxRefl M e) (hnc : r * r' ≠ r' * r) :
    ∃ (p₀ p₁ p₂ : Fin m) (V : DVec m ≃ₗ[ZMod 3] DVec m),
      p₁.val = p₀.val + 1 ∧ p₂.val = p₀.val + 2 ∧ V ∈ dEven m ∧
      V * qtwoDB21_lin βL r * V⁻¹ = dTau m false p₀ p₁ ∧
      V * qtwoDB21_lin βL r' * V⁻¹ = dTau m false p₁ p₂ := by
  classical
  have hXc := qtwoDB21_X_le_centralizer hbase hcoords hdel
  have hrb' : r b' = b' := qtwoDB21_fixes_b' hXc hrA
  have hr'b' : r' b' = b' := qtwoDB21_fixes_b' hXc hr'A
  obtain ⟨sgn, i, j, hij, hact⟩ := hcoords.coxRoot r hrC
  obtain ⟨sgn', i', j', hi'j', hact'⟩ := hcoords.coxRoot r' hr'C
  have hfix : dTau m sgn i j (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    have h1 : βL (Additive.ofMul (r b')) = βL (Additive.ofMul b') := by rw [hrb']
    rw [hact b', hdel.coord] at h1
    exact h1
  obtain ⟨hci, hcj⟩ := qtwoDB21_dTau_fixes_single hij hfix
  have hfix' : dTau m sgn' i' j' (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    have h1 : βL (Additive.ofMul (r' b')) = βL (Additive.ofMul b') := by rw [hr'b']
    rw [hact' b', hdel.coord] at h1
    exact h1
  obtain ⟨hci', hcj'⟩ := qtwoDB21_dTau_fixes_single hi'j' hfix'
  have hnc' : dTau m sgn i j * dTau m sgn' i' j' ≠ dTau m sgn' i' j' * dTau m sgn i j := by
    intro h
    apply hnc
    apply qtwoDB21_lin_injective βL
    rw [map_mul, map_mul, qtwoDB21_lin_of_action hact, qtwoDB21_lin_of_action hact']
    exact h
  obtain ⟨p₀, p₁, p₂, hp1, hp2, -, hc0, hc1, hc2, U, hU, -, hconj1, hconj2⟩ :=
    Sl.exists_conj_pair_of_noncomm_fix (by omega : 6 ≤ m) hij hi'j' sgn sgn' hnc' hci hcj
      hci' hcj'
  refine ⟨p₀, p₁, p₂, U⁻¹, hp1, hp2, (dEven m).inv_mem hU, ?_, ?_⟩
  · rw [qtwoDB21_lin_of_action hact, ← hconj1]
    group
  · rw [qtwoDB21_lin_of_action hact', ← hconj2]
    group

private lemma qtwoDB21_avoid_triple {ε : Bool} {x y p₀ p₁ p₂ : Fin m}
    (hxy : x ≠ y) (hp0p1 : p₀ ≠ p₁) (hp1p2 : p₁ ≠ p₂) (hp0p2 : p₀ ≠ p₂)
    (h1 : dTau m ε x y * dTau m false p₀ p₁ = dTau m false p₀ p₁ * dTau m ε x y)
    (h2 : dTau m ε x y * dTau m false p₁ p₂ = dTau m false p₁ p₂ * dTau m ε x y) :
    x ≠ p₀ ∧ x ≠ p₁ ∧ x ≠ p₂ ∧ y ≠ p₀ ∧ y ≠ p₁ ∧ y ≠ p₂ := by
  have hc1 := fun v => congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T v) h1
  have hc2 := fun v => congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T v) h2
  rcases (dTau_comm_iff m ε false hxy hp0p1).mp hc1 with hd | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rcases (dTau_comm_iff m ε false hxy hp1p2).mp hc2 with he | ⟨f1, f2⟩ | ⟨f1, f2⟩
    · exact ⟨hd.1, hd.2.1, he.2.1, hd.2.2.1, hd.2.2.2, he.2.2.2⟩
    · exact absurd f1 hd.2.1
    · exact absurd f2 hd.2.2.2
  · rcases (dTau_comm_iff m ε false hxy hp1p2).mp hc2 with he | ⟨f1, f2⟩ | ⟨f1, f2⟩
    · exact absurd e2 he.2.2.1
    · exact absurd (e1.symm.trans f1) hp0p1
    · exact absurd (e1.symm.trans f1) hp0p2
  · rcases (dTau_comm_iff m ε false hxy hp1p2).mp hc2 with he | ⟨f1, f2⟩ | ⟨f1, f2⟩
    · exact absurd e1 he.1
    · exact absurd (e2.symm.trans f2) hp0p2
    · exact absurd (e1.symm.trans f1) hp1p2

private lemma qtwoDB21_sign_correction {ε₃ ε₄ : Bool} {y x z : Fin m}
    (hyx : y ≠ x) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ D : DVec m ≃ₗ[ZMod 3] DVec m, D ∈ dEven m ∧
      D * dTau m ε₃ y x * D⁻¹ = dTau m false y x ∧
      D * dTau m ε₄ x z * D⁻¹ = dTau m false x z ∧
      (D = 1 ∨ D = dSign m y z ∨ D = dSign m x z ∨ D = dSign m x y) := by
  cases ε₃ <;> cases ε₄
  · exact ⟨1, (dEven m).one_mem, by simp, by simp, Or.inl rfl⟩
  · refine ⟨dSign m x y, qtwoDB21_dSign_mem_dEven m hyx.symm, ?_, ?_, Or.inr (Or.inr (Or.inr rfl))⟩
    · exact Sl.dSign_conj m (p := x) (q := y) (a := y) (b := x) hyx false false (by
        rw [if_pos (Or.inr rfl), if_pos (Or.inl rfl)]; decide)
    · exact Sl.dSign_conj m (p := x) (q := y) (a := x) (b := z) hxz true false (by
        rw [if_pos (Or.inl rfl), if_neg (fun h => h.elim hxz.symm hyz.symm)]; decide)
  · refine ⟨dSign m x z, qtwoDB21_dSign_mem_dEven m hxz, ?_, ?_, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact Sl.dSign_conj m (p := x) (q := z) (a := y) (b := x) hyx true false (by
        rw [if_neg (fun h => h.elim hyx hyz), if_pos (Or.inl rfl)]; decide)
    · exact Sl.dSign_conj m (p := x) (q := z) (a := x) (b := z) hxz false false (by
        rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl)]; decide)
  · refine ⟨dSign m y z, qtwoDB21_dSign_mem_dEven m hyz, ?_, ?_, Or.inr (Or.inl rfl)⟩
    · exact Sl.dSign_conj m (p := y) (q := z) (a := y) (b := x) hyx true false (by
        rw [if_pos (Or.inl rfl), if_neg (fun h => h.elim hyx.symm hxz)]; decide)
    · exact Sl.dSign_conj m (p := y) (q := z) (a := x) (b := z) hxz true false (by
        rw [if_neg (fun h => h.elim hyx.symm hxz), if_pos (Or.inr rfl)]; decide)

theorem ggQTwoDUnit_X_far2 (hEA : GGQTwoEdgeAmbientInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b') :
    ∀ r₁ ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r₁ ∈ ggCoxRefl M e →
      ∀ r₂ ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r₂ ∈ ggCoxRefl M e →
        ∀ r₃ ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r₃ ∈ ggCoxRefl M e →
          ∀ r₄ ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r₄ ∈ ggCoxRefl M e →
            r₁ * r₂ ≠ r₂ * r₁ → r₃ * r₄ ≠ r₄ * r₃ → r₁ * r₃ = r₃ * r₁ → r₁ * r₄ = r₄ * r₁ →
              r₂ * r₃ = r₃ * r₂ → r₂ * r₄ = r₄ * r₂ →
                ∀ y ∈ ggRankTwoIn (qtwoDelX ψ c g) Bs r₁ r₂,
                  ∀ z ∈ ggRankTwoIn (qtwoDelX ψ c g) Bs r₃ r₄, y * z = z * y := by
  intro r₁ hr₁A hr₁C r₂ hr₂A hr₂C r₃ hr₃A hr₃C r₄ hr₄A hr₄C
    hnc12 hnc34 hc13 hc14 hc23 hc24 y hy z hz
  classical
  obtain ⟨p₀, p₁, p₂, V, hVp1, hVp2, hVmem, hVr1, hVr2⟩ :=
    qtwoDB21_pair_lin hbase hcoords hdel hm hr₁A hr₁C hr₂A hr₂C hnc12
  have hp0p1 : p₀ ≠ p₁ := fun h => by have := congrArg Fin.val h; omega
  have hp1p2 : p₁ ≠ p₂ := fun h => by have := congrArg Fin.val h; omega
  have hp0p2 : p₀ ≠ p₂ := fun h => by have := congrArg Fin.val h; omega
  obtain ⟨a₀, ha₀J, ha₀V⟩ := hcoords.join_onto V hVmem
  have ha₀lin : qtwoDB21_lin βL a₀ = V := qtwoDB21_lin_of_action ha₀V
  let r₁' : MulAut ↥Bs := a₀ * r₁ * a₀⁻¹
  let r₂' : MulAut ↥Bs := a₀ * r₂ * a₀⁻¹
  let r₃' : MulAut ↥Bs := a₀ * r₃ * a₀⁻¹
  let r₄' : MulAut ↥Bs := a₀ * r₄ * a₀⁻¹
  have hlin1 : qtwoDB21_lin βL r₁' = dTau m false p₀ p₁ := by
    rw [qtwoDB21_lin_conj a₀ r₁, ha₀lin, hVr1]
  have hlin2 : qtwoDB21_lin βL r₂' = dTau m false p₁ p₂ := by
    rw [qtwoDB21_lin_conj a₀ r₂, ha₀lin, hVr2]
  obtain ⟨s₃, a₃, b₃, hab₃, hact₃⟩ := hcoords.coxRoot r₃ hr₃C
  obtain ⟨s₄, a₄, b₄, hab₄, hact₄⟩ := hcoords.coxRoot r₄ hr₄C
  obtain ⟨e₃, x₃, y₃, hx₃y₃, hconj3⟩ := Sl.conj_dTau_exists m hVmem s₃ hab₃
  obtain ⟨e₄, x₄, y₄, hx₄y₄, hconj4⟩ := Sl.conj_dTau_exists m hVmem s₄ hab₄
  have hVr3 : V * qtwoDB21_lin βL r₃ * V⁻¹ = dTau m e₃ x₃ y₃ := by
    rw [qtwoDB21_lin_of_action hact₃, hconj3]
  have hVr4 : V * qtwoDB21_lin βL r₄ * V⁻¹ = dTau m e₄ x₄ y₄ := by
    rw [qtwoDB21_lin_of_action hact₄, hconj4]
  have hlin3' : qtwoDB21_lin βL r₃' = dTau m e₃ x₃ y₃ := by
    rw [qtwoDB21_lin_conj a₀ r₃, ha₀lin, hVr3]
  have hlin4' : qtwoDB21_lin βL r₄' = dTau m e₄ x₄ y₄ := by
    rw [qtwoDB21_lin_conj a₀ r₄, ha₀lin, hVr4]
  have hlincomm31 : dTau m e₃ x₃ y₃ * dTau m false p₀ p₁ =
      dTau m false p₀ p₁ * dTau m e₃ x₃ y₃ := by
    rw [← hlin3', ← hlin1]
    exact qtwoDB21_lin_conj_comm (a := a₀) hc13.symm
  have hlincomm32 : dTau m e₃ x₃ y₃ * dTau m false p₁ p₂ =
      dTau m false p₁ p₂ * dTau m e₃ x₃ y₃ := by
    rw [← hlin3', ← hlin2]
    exact qtwoDB21_lin_conj_comm (a := a₀) hc23.symm
  have hlincomm41 : dTau m e₄ x₄ y₄ * dTau m false p₀ p₁ =
      dTau m false p₀ p₁ * dTau m e₄ x₄ y₄ := by
    rw [← hlin4', ← hlin1]
    exact qtwoDB21_lin_conj_comm (a := a₀) hc14.symm
  have hlincomm42 : dTau m e₄ x₄ y₄ * dTau m false p₁ p₂ =
      dTau m false p₁ p₂ * dTau m e₄ x₄ y₄ := by
    rw [← hlin4', ← hlin2]
    exact qtwoDB21_lin_conj_comm (a := a₀) hc24.symm
  have hnc34' : dTau m e₃ x₃ y₃ * dTau m e₄ x₄ y₄ ≠ dTau m e₄ x₄ y₄ * dTau m e₃ x₃ y₃ := by
    intro h
    apply hnc34
    have h34 : r₃' * r₄' = r₄' * r₃' := by
      apply qtwoDB21_lin_injective βL
      rw [map_mul (qtwoDB21_lin βL) r₃' r₄', map_mul (qtwoDB21_lin βL) r₄' r₃', hlin3', hlin4']
      exact h
    have h' := congrArg (fun w => a₀⁻¹ * w * a₀) h34
    rwa [show a₀⁻¹ * ((a₀ * r₃ * a₀⁻¹) * (a₀ * r₄ * a₀⁻¹)) * a₀ = r₃ * r₄ by group,
      show a₀⁻¹ * ((a₀ * r₄ * a₀⁻¹) * (a₀ * r₃ * a₀⁻¹)) * a₀ = r₄ * r₃ by group] at h'
  obtain ⟨y₂, x₂, z₂, hy₂x₂, hx₂z₂, hy₂z₂, hchain3, hchain4⟩ :=
    Sl.exists_chain m hx₃y₃ hx₄y₄ e₃ e₄ hnc34'
  have hlincomm31' : dTau m e₃ y₂ x₂ * dTau m false p₀ p₁ =
      dTau m false p₀ p₁ * dTau m e₃ y₂ x₂ := by rw [← hchain3]; exact hlincomm31
  have hlincomm32' : dTau m e₃ y₂ x₂ * dTau m false p₁ p₂ =
      dTau m false p₁ p₂ * dTau m e₃ y₂ x₂ := by rw [← hchain3]; exact hlincomm32
  have hlincomm41' : dTau m e₄ x₂ z₂ * dTau m false p₀ p₁ =
      dTau m false p₀ p₁ * dTau m e₄ x₂ z₂ := by rw [← hchain4]; exact hlincomm41
  have hlincomm42' : dTau m e₄ x₂ z₂ * dTau m false p₁ p₂ =
      dTau m false p₁ p₂ * dTau m e₄ x₂ z₂ := by rw [← hchain4]; exact hlincomm42
  obtain ⟨hy₂p0, hy₂p1, hy₂p2, hx₂p0, hx₂p1, hx₂p2⟩ :=
    qtwoDB21_avoid_triple hy₂x₂ hp0p1 hp1p2 hp0p2 hlincomm31' hlincomm32'
  obtain ⟨-, -, -, hz₂p0, hz₂p1, hz₂p2⟩ :=
    qtwoDB21_avoid_triple hx₂z₂ hp0p1 hp1p2 hp0p2 hlincomm41' hlincomm42'
  obtain ⟨D, hDmem, hD3, hD4, hDcases⟩ :=
    qtwoDB21_sign_correction (ε₃ := e₃) (ε₄ := e₄) (y := y₂) (x := x₂) (z := z₂)
      hy₂x₂ hx₂z₂ hy₂z₂
  let w₀ : DVec m ≃ₗ[ZMod 3] DVec m := D * V
  have hw₀mem : w₀ ∈ dEven m := (dEven m).mul_mem hDmem hVmem
  obtain ⟨a₁, ha₁J, ha₁w⟩ := hcoords.join_onto w₀ hw₀mem
  have ha₁lin : qtwoDB21_lin βL a₁ = w₀ := qtwoDB21_lin_of_action ha₁w
  obtain ⟨n₁, -, hn₁N, hn₁act⟩ := exists_lift_of_mem_ggAutomizerJoin ha₁J
  have hDcomm1 : D * dTau m false p₀ p₁ * D⁻¹ = dTau m false p₀ p₁ := by
    rcases hDcases with rfl | rfl | rfl | rfl
    · simp
    · exact qtwoDB21_dSign_comm_dTau_false hy₂p0.symm hz₂p0.symm hy₂p1.symm hz₂p1.symm
    · exact qtwoDB21_dSign_comm_dTau_false hx₂p0.symm hz₂p0.symm hx₂p1.symm hz₂p1.symm
    · exact qtwoDB21_dSign_comm_dTau_false hx₂p0.symm hy₂p0.symm hx₂p1.symm hy₂p1.symm
  have hDcomm2 : D * dTau m false p₁ p₂ * D⁻¹ = dTau m false p₁ p₂ := by
    rcases hDcases with rfl | rfl | rfl | rfl
    · simp
    · exact qtwoDB21_dSign_comm_dTau_false hy₂p1.symm hz₂p1.symm hy₂p2.symm hz₂p2.symm
    · exact qtwoDB21_dSign_comm_dTau_false hx₂p1.symm hz₂p1.symm hx₂p2.symm hz₂p2.symm
    · exact qtwoDB21_dSign_comm_dTau_false hx₂p1.symm hy₂p1.symm hx₂p2.symm hy₂p2.symm
  let r₁'' : MulAut ↥Bs := a₁ * r₁ * a₁⁻¹
  let r₂'' : MulAut ↥Bs := a₁ * r₂ * a₁⁻¹
  let r₃'' : MulAut ↥Bs := a₁ * r₃ * a₁⁻¹
  let r₄'' : MulAut ↥Bs := a₁ * r₄ * a₁⁻¹
  have hlin1'' : qtwoDB21_lin βL r₁'' = dTau m false p₀ p₁ := by
    rw [qtwoDB21_lin_conj a₁ r₁, ha₁lin, show w₀ = D * V from rfl, qtwoDB21_w₀_conj D V,
      hVr1, hDcomm1]
  have hlin2'' : qtwoDB21_lin βL r₂'' = dTau m false p₁ p₂ := by
    rw [qtwoDB21_lin_conj a₁ r₂, ha₁lin, show w₀ = D * V from rfl, qtwoDB21_w₀_conj D V,
      hVr2, hDcomm2]
  have hlin3'' : qtwoDB21_lin βL r₃'' = dTau m false y₂ x₂ := by
    rw [qtwoDB21_lin_conj a₁ r₃, ha₁lin, show w₀ = D * V from rfl, qtwoDB21_w₀_conj D V,
      hVr3, hchain3, hD3]
  have hlin4'' : qtwoDB21_lin βL r₄'' = dTau m false x₂ z₂ := by
    rw [qtwoDB21_lin_conj a₁ r₄, ha₁lin, show w₀ = D * V from rfl, qtwoDB21_w₀_conj D V,
      hVr4, hchain4, hD4]
  have hr1''eq := qtwoDB21_perm_of_lin hcoords hlin1''
  have hr2''eq := qtwoDB21_perm_of_lin hcoords hlin2''
  have hr3''eq := qtwoDB21_perm_of_lin hcoords hlin3''
  have hr4''eq := qtwoDB21_perm_of_lin hcoords hlin4''
  have hr1''L : r₁'' ∈ ggAutomizer L Bs := by rw [hr1''eq]; exact (ε (Equiv.swap p₀ p₁)).2
  have hr2''L : r₂'' ∈ ggAutomizer L Bs := by rw [hr2''eq]; exact (ε (Equiv.swap p₁ p₂)).2
  have hr3''L : r₃'' ∈ ggAutomizer L Bs := by rw [hr3''eq]; exact (ε (Equiv.swap y₂ x₂)).2
  have hr4''L : r₄'' ∈ ggAutomizer L Bs := by rw [hr4''eq]; exact (ε (Equiv.swap x₂ z₂)).2
  have hr1''C : r₁'' ∈ ggCoxRefl M e := by rw [hr1''eq]; exact qtwoDB21_cox_of_perm hcoords hp0p1
  have hr2''C : r₂'' ∈ ggCoxRefl M e := by rw [hr2''eq]; exact qtwoDB21_cox_of_perm hcoords hp1p2
  have hr3''C : r₃'' ∈ ggCoxRefl M e := by rw [hr3''eq]; exact qtwoDB21_cox_of_perm hcoords hy₂x₂
  have hr4''C : r₄'' ∈ ggCoxRefl M e := by rw [hr4''eq]; exact qtwoDB21_cox_of_perm hcoords hx₂z₂
  have hnc12'' : r₁'' * r₂'' ≠ r₂'' * r₁'' := qtwoDB21_conj_ne (a := a₁) hnc12
  have hnc34'' : r₃'' * r₄'' ≠ r₄'' * r₃'' := qtwoDB21_conj_ne (a := a₁) hnc34
  have hbound1 := qtwoDB21_rankTwo_le hEA hcfg hm hM hbase hp0p1 hp1p2 hp0p2
    hr1''L hr1''C hr2''L hr2''C hr1''eq hr2''eq hnc12''
  have hbound2 := qtwoDB21_rankTwo_le hEA hcfg hm hM hbase hy₂x₂ hx₂z₂ hy₂z₂
    hr3''L hr3''C hr4''L hr4''C hr3''eq hr4''eq hnc34''
  have hdisj : Disjoint ({p₀, p₁, p₂} : Finset (Fin m)) ({y₂, x₂, z₂} : Finset (Fin m)) := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk hk'
    rcases hk with rfl | rfl | rfl <;> rcases hk' with h | h | h <;> simp_all
  have hblocks : ∀ u ∈ (coordBlockSU F0 2 1 ({p₀, p₁, p₂} : Finset (Fin m))).map ψ,
      ∀ w ∈ (coordBlockSU F0 2 1 ({y₂, x₂, z₂} : Finset (Fin m))).map ψ, u * w = w * u := by
    rintro u ⟨u', hu', rfl⟩ w ⟨w', hw', rfl⟩
    rw [← map_mul, ← map_mul, ggQTwoDUnit_coordBlockSU_comm hdisj hu' hw']
  have hrank1 : ggRankTwoIn (qtwoDelX ψ c g) Bs r₁ r₂ = ggRankTwo Bs r₁ r₂ :=
    (ggQTwoDUnit_X_rankTwo hEA hcfg hm hM hbase hcoords hdel r₁ hr₁A hr₁C r₂ hr₂A hr₂C hnc12).symm
  have hrank2 : ggRankTwoIn (qtwoDelX ψ c g) Bs r₃ r₄ = ggRankTwo Bs r₃ r₄ :=
    (ggQTwoDUnit_X_rankTwo hEA hcfg hm hM hbase hcoords hdel r₃ hr₃A hr₃C r₄ hr₄A hr₄C hnc34).symm
  have hmap1 : (ggRankTwo Bs r₁ r₂).map (MulAut.conj n₁).toMonoidHom = ggRankTwo Bs r₁'' r₂'' :=
    ggRankTwo_map_conj hn₁act r₁ r₂
  have hmap2 : (ggRankTwo Bs r₃ r₄).map (MulAut.conj n₁).toMonoidHom = ggRankTwo Bs r₃'' r₄'' :=
    ggRankTwo_map_conj hn₁act r₃ r₄
  rw [hrank1] at hy
  rw [hrank2] at hz
  have hy'' : n₁ * y * n₁⁻¹ ∈ ggRankTwo Bs r₁'' r₂'' := by
    rw [← hmap1]
    exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
  have hz'' : n₁ * z * n₁⁻¹ ∈ ggRankTwo Bs r₃'' r₄'' := by
    rw [← hmap2]
    exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hcomm'' := hblocks (n₁ * y * n₁⁻¹) (hbound1 hy'') (n₁ * z * n₁⁻¹) (hbound2 hz'')
  have hkey : n₁ * (y * z) * n₁⁻¹ = n₁ * (z * y) * n₁⁻¹ := by
    calc n₁ * (y * z) * n₁⁻¹ = (n₁ * y * n₁⁻¹) * (n₁ * z * n₁⁻¹) := by group
      _ = (n₁ * z * n₁⁻¹) * (n₁ * y * n₁⁻¹) := hcomm''
      _ = n₁ * (z * y) * n₁⁻¹ := by group
  have h2 := congrArg (fun w => n₁⁻¹ * w * n₁) hkey
  rwa [show n₁⁻¹ * (n₁ * (y * z) * n₁⁻¹) * n₁ = y * z by group,
    show n₁⁻¹ * (n₁ * (z * y) * n₁⁻¹) * n₁ = z * y by group] at h2

end CFSG.StandardType.QTwo

end
