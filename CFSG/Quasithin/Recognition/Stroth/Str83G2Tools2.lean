module

public import CFSG.Quasithin.SteinbergCDExactPlaneWreathAggregate
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifySylow
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

theorem topmost_factor_eq_bot
    {H : Type} [Group H] [Finite H]
    {X V D S N : Subgroup H} {w : H} [N.Normal]
    (hX : X.Normal) (hXe : IsElemAbelian 2 X)
    (hNX : N ≤ X)
    (hVX : V ≤ X)
    (hgen : X = conjClosure V ⊤)
    (hDodd : Odd (Nat.card D))
    (hD : D ≤ oTwoUpper (⊤ : Subgroup H))
    (hDV : D ≤ Subgroup.centralizer (V : Set H))
    (hS : IsSylowTwoOf S ⊤)
    (hVS : S ≤ Subgroup.normalizer (V : Set H))
    (hSw : S ⊔ conjugate S w = ⊤)
    (hwD : w ∈ Subgroup.normalizer (D : Set H))
    (hO2 : ⁅X, oTwoUpper (⊤ : Subgroup H)⁆ ≤ N)
    (hC : N ⊓ Subgroup.centralizer (D : Set H) = ⊥) :
    N = ⊥ := by
  classical
  have hH : (⊤ : Subgroup H) = oTwoUpper (⊤ : Subgroup H) ⊔ S :=
    CFSG.Quasithin.H13.eq_oTwoUpper_sup_of_isSylowTwoOf hS
  have hNnorm : (⊤ : Subgroup H) ≤ Subgroup.normalizer (N : Set H) :=
    (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  have hVN_normal : (V ⊔ N).Normal := by
    have hS_le : S ≤ Subgroup.normalizer ((V ⊔ N : Subgroup H) : Set H) :=
      F1.le_normalizer_sup hVS (le_top.trans hNnorm)
    have hO2_le : oTwoUpper (⊤ : Subgroup H) ≤
        Subgroup.normalizer ((V ⊔ N : Subgroup H) : Set H) := by
      intro h hh
      have hconjN : conjugate N h = N :=
        conjugate_eq_self_of_mem_normalizer (hNnorm (Subgroup.mem_top h))
      have hconjV_le : conjugate V h ≤ V ⊔ N := by
        intro x hx
        rw [mem_conjugate_iff] at hx
        have hyX : h * x * h⁻¹ ∈ X := hVX hx
        have hcomm : ⁅h * x * h⁻¹, h⁆ ∈ N :=
          hO2 (Subgroup.commutator_mem_commutator hyX hh)
        have hcomm' : h⁻¹ * ⁅h * x * h⁻¹, h⁆ * h ∈ N := by
          simpa using (inferInstance : N.Normal).conj_mem (⁅h * x * h⁻¹, h⁆) hcomm h⁻¹
        have hxeq : x = (h⁻¹ * ⁅h * x * h⁻¹, h⁆ * h) * (h * x * h⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [hxeq]
        exact (V ⊔ N).mul_mem (Subgroup.mem_sup_right hcomm') (Subgroup.mem_sup_left hx)
      have hconj_le : conjugate (V ⊔ N) h ≤ V ⊔ N := by
        rw [conjugate, Subgroup.map_sup]
        change conjugate V h ⊔ conjugate N h ≤ V ⊔ N
        rw [hconjN]
        exact sup_le hconjV_le le_sup_right
      have hcard : Nat.card ↥(conjugate (V ⊔ N) h) = Nat.card ↥(V ⊔ N) := by
        rw [conjugate]
        exact Subgroup.card_map_of_injective (f := (MulAut.conj h⁻¹).toMonoidHom)
          (MulAut.conj h⁻¹).injective
      have hEq : conjugate (V ⊔ N) h = V ⊔ N :=
        Subgroup.eq_of_le_of_card_ge hconj_le (le_of_eq hcard.symm)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hx' : x ∈ conjugate (V ⊔ N) h := by rw [hEq]; exact hx
        exact (mem_conjugate_iff (V ⊔ N) h x).mp hx'
      · intro hx
        have hx' : x ∈ conjugate (V ⊔ N) h := (mem_conjugate_iff (V ⊔ N) h x).mpr hx
        rwa [hEq] at hx'
    have hH_le : (⊤ : Subgroup H) ≤ Subgroup.normalizer ((V ⊔ N : Subgroup H) : Set H) := by
      rw [hH]
      exact sup_le hO2_le hS_le
    exact Subgroup.Normal.mk fun n hn g =>
      (Subgroup.mem_normalizer_iff.mp (hH_le (Subgroup.mem_top g)) n).mp hn
  have hX_eq : X = V ⊔ N := by
    apply le_antisymm ?_ (sup_le hVX hNX)
    rw [hgen]
    exact conjClosure_le fun h _ v hv =>
      hVN_normal.conj_mem v (Subgroup.mem_sup_left hv) h
  have hVinfN : V ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxbot : x ∈ N ⊓ Subgroup.centralizer (D : Set H) :=
      ⟨hx.2, (Subgroup.le_centralizer_iff.mp hDV) hx.1⟩
    rw [hC] at hxbot
    exact hxbot
  set C : Subgroup H := X ⊓ Subgroup.centralizer (D : Set H) with hCdef
  have hcommD : ⁅X, D⁆ ≤ N :=
    (Subgroup.commutator_mono le_rfl hD).trans hO2
  have hdec := CFSG.Quasithin.SteinbergCD.le_commutator_sup_centralizer_of_odd
    (A := X) (P := D) hXe (le_top.trans ((Subgroup.normalizer_eq_top_iff.mpr hX).ge)) hDodd
  have hX_eq_NC : X = N ⊔ C := by
    apply le_antisymm
    · exact hdec.trans (sup_le_sup hcommD le_rfl)
    · exact sup_le hNX inf_le_left
  have hCinfN : C ⊓ N = ⊥ := by
    rw [hCdef, inf_assoc, inf_comm (Subgroup.centralizer (D : Set H)) N, hC, inf_bot_eq]
  have hVC : V ≤ C := le_inf hVX (Subgroup.le_centralizer_iff.mp hDV)
  letI : CommGroup ↥X := commGroupOfElemAbelian hXe
  have hcommX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    have h1 : (⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := mul_comm _ _
    exact congrArg Subtype.val h1
  have hN_le_CV : N ≤ Subgroup.centralizer (V : Set H) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcommX n (hNX hn) v (hVX hv)).symm
  have hN_le_CC : N ≤ Subgroup.centralizer (C : Set H) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hcommX n (hNX hn) c hc.1).symm
  have hcardV := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    V N (hN_le_CV.trans (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr hVinfN)
  have hcardC := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    C N (hN_le_CC.trans (Subgroup.centralizer_le_normalizer _)) (disjoint_iff.mpr hCinfN)
  have hC_sup_N : C ⊔ N = X := by rw [sup_comm, hX_eq_NC]
  have hcard_eq : Nat.card ↥V = Nat.card ↥C := by
    have h1 : Nat.card ↥V * Nat.card ↥N = Nat.card ↥C * Nat.card ↥N := by
      rw [← hcardV, ← hcardC, ← hX_eq, ← hC_sup_N]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hV_eq_C : V = C := Subgroup.eq_of_le_of_card_ge hVC (le_of_eq hcard_eq.symm)
  have hC_normal : C.Normal := by
    have hS_le : S ≤ Subgroup.normalizer (C : Set H) := by
      rw [← hV_eq_C]
      exact hVS
    have hw_le : w ∈ Subgroup.normalizer (C : Set H) := by
      have hwX : w ∈ Subgroup.normalizer (X : Set H) :=
        (Subgroup.normalizer_eq_top_iff.mpr hX).ge (Subgroup.mem_top w)
      have hwCD : w ∈ Subgroup.normalizer
          (Subgroup.centralizer (D : Set H) : Set H) :=
        F7.normalizer_le_normalizer_centralizer D hwD
      exact A4.mem_normalizer_inf hwX hwCD
    have hH_le : (⊤ : Subgroup H) ≤ Subgroup.normalizer (C : Set H) := by
      rw [← hSw]
      refine sup_le hS_le ?_
      intro x hx
      have hwx : w * x * w⁻¹ ∈ S := (mem_conjugate_iff S w x).mp hx
      have hwxN : w * x * w⁻¹ ∈ Subgroup.normalizer (C : Set H) := hS_le hwx
      have h1 : w⁻¹ * (w * x * w⁻¹) ∈ Subgroup.normalizer (C : Set H) :=
        (Subgroup.normalizer (C : Set H)).mul_mem
          (Subgroup.inv_mem _ hw_le) hwxN
      have h2 : w⁻¹ * (w * x * w⁻¹) * w ∈ Subgroup.normalizer (C : Set H) :=
        (Subgroup.normalizer (C : Set H)).mul_mem h1 hw_le
      rwa [show w⁻¹ * (w * x * w⁻¹) * w = x by group] at h2
    exact Subgroup.Normal.mk fun n hn g =>
      (Subgroup.mem_normalizer_iff.mp (hH_le (Subgroup.mem_top g)) n).mp hn
  have hX_le_V : X ≤ V := by
    rw [hgen]
    refine conjClosure_le fun h _ v hv => ?_
    rw [hV_eq_C] at hv ⊢
    exact hC_normal.conj_mem v hv h
  have hNle : N ≤ V := hNX.trans hX_le_V
  exact le_bot_iff.mp (by rw [← hVinfN]; exact le_inf hNle le_rfl)

theorem topmost_factor_eq {H : Type} [Group H] [Finite H]
    {X V D S N L : Subgroup H} {w : H} [L.Normal] [N.Normal]
    (hX : X.Normal) (hXe : IsElemAbelian 2 X)
    (hLN : L ≤ N) (hNX : N ≤ X) (hVX : V ≤ X)
    (hgen : X = conjClosure V ⊤)
    (hDodd : Odd (Nat.card D))
    (hD : D ≤ oTwoUpper (⊤ : Subgroup H))
    (hDV : D ≤ Subgroup.centralizer (V : Set H))
    (hS : IsSylowTwoOf S ⊤)
    (hVS : S ≤ Subgroup.normalizer (V : Set H))
    (hSw : S ⊔ conjugate S w = ⊤)
    (hwD : w ∈ Subgroup.normalizer (D : Set H))
    (hO2 : ⁅X, oTwoUpper (⊤ : Subgroup H)⁆ ≤ N)
    (hC : ∀ x ∈ N, (∀ d ∈ D, x * d * x⁻¹ * d⁻¹ ∈ L) → x ∈ L) :
    N = L := by
  classical
  let Hq : Type := H ⧸ L
  let π : H →* Hq := QuotientGroup.mk' L
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective L
  let Xq : Subgroup Hq := X.map π
  let Vq : Subgroup Hq := V.map π
  let Dq : Subgroup Hq := D.map π
  let Sq : Subgroup Hq := S.map π
  let Nq : Subgroup Hq := N.map π
  have hXq : Xq.Normal := hX.map π hπ
  have hXq_e : IsElemAbelian 2 Xq := hXe.map π
  have hNq_le_Xq : Nq ≤ Xq := Subgroup.map_mono hNX
  have hVq_le_Xq : Vq ≤ Xq := Subgroup.map_mono hVX
  have hgenq : Xq = conjClosure Vq ⊤ := by
    rw [show Xq = (conjClosure V ⊤).map π from by rw [← hgen]]
    rw [map_conjClosure_eq, Subgroup.map_top_of_surjective π hπ]
  have hDq_odd : Odd (Nat.card Dq) :=
    hDodd.of_dvd_nat (Subgroup.card_map_dvd D π)
  have hDq_le_oTwo : Dq ≤ oTwoUpper (⊤ : Subgroup Hq) := by
    have h1 : Dq ≤ (oTwoUpper (⊤ : Subgroup H)).map π := Subgroup.map_mono hD
    rwa [show (oTwoUpper (⊤ : Subgroup H)).map π = oTwoUpper (⊤ : Subgroup Hq) from by
      rw [← oTwoUpper_map π ⊤, Subgroup.map_top_of_surjective π hπ]] at h1
  have hDq_Vq : Dq ≤ Subgroup.centralizer (Vq : Set Hq) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    have hcomm : d * v = v * d := ((Subgroup.mem_centralizer_iff.mp (hDV hd)) v hv).symm
    have hcommπ : π (d * v) = π (v * d) := congrArg π hcomm
    simpa [map_mul] using hcommπ.symm
  have hSq_sylow : IsSylowTwoOf Sq ⊤ := by
    have := CFSG.GH74.QTGen4.DSGen4.isSylowTwoOf_map (φ := π) hS
    rwa [Subgroup.map_top_of_surjective π hπ] at this
  have hSq_Vq : Sq ≤ Subgroup.normalizer (Vq : Set Hq) :=
    (Subgroup.map_mono hVS).trans (Subgroup.le_normalizer_map π)
  have hSq_w : Sq ⊔ conjugate Sq (π w) = ⊤ := by
    have h := congrArg (Subgroup.map π) hSw
    rw [Subgroup.map_sup, CFSG.map_conjugate π S w, Subgroup.map_top_of_surjective π hπ] at h
    exact h
  have hwDq : π w ∈ Subgroup.normalizer (Dq : Set Hq) :=
    Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hwD)
  have hO2q : ⁅Xq, oTwoUpper (⊤ : Subgroup Hq)⁆ ≤ Nq := by
    have h := Subgroup.map_commutator (H₁ := X) (H₂ := oTwoUpper (⊤ : Subgroup H)) π
    rw [show (oTwoUpper (⊤ : Subgroup H)).map π = oTwoUpper (⊤ : Subgroup Hq) from by
      rw [← oTwoUpper_map π ⊤, Subgroup.map_top_of_surjective π hπ]] at h
    rw [← h]
    exact Subgroup.map_mono hO2
  have hCq : Nq ⊓ Subgroup.centralizer (Dq : Set Hq) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨x0, hx0N, rfl⟩ := Subgroup.mem_map.mp hxN
    have hx0L : x0 ∈ L := by
      apply hC x0 hx0N
      intro d hd
      have hdDq : π d ∈ Dq := Subgroup.mem_map_of_mem π hd
      have hcent := (Subgroup.mem_centralizer_iff.mp hxC) (π d) hdDq
      have h1 : π (x0 * d * x0⁻¹ * d⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcent]
        group
      exact (QuotientGroup.eq_one_iff (N := L) (x := x0 * d * x0⁻¹ * d⁻¹)).mp h1
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff (N := L) (x := x0)).mpr hx0L)
  have hNq_bot : Nq = ⊥ :=
    topmost_factor_eq_bot hXq hXq_e hNq_le_Xq hVq_le_Xq hgenq hDq_odd hDq_le_oTwo
      hDq_Vq hSq_sylow hSq_Vq hSq_w hwDq hO2q hCq
  apply le_antisymm _ hLN
  intro n hn
  have hnq : π n ∈ Nq := Subgroup.mem_map_of_mem π hn
  rw [hNq_bot] at hnq
  rw [← QuotientGroup.eq_one_iff]
  exact Subgroup.mem_bot.mp hnq

end CFSG.Quasithin.Stroth

end
