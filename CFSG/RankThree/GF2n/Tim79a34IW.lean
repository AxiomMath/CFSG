module

public import CFSG.RankThree.GF2n.Tim79a34Natural
public import CFSG.RankThree.GF2n.Tim79a34TwWSplit
public import CFSG.RankThree.GF2n.Tim79a34TwBound

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection
  CFSG.Timmesfeld.Transvection.ModelRank CFSG.LieType.Universal.Symplectic
open Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

theorem iw_projZ_injective {V H : Subgroup G} (hZ : Subgroup.center (Xbar V H) = ⊥) :
    Function.Injective (projZ V H) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : x ∈ Subgroup.center (Xbar V H) := (QuotientGroup.eq_one_iff x).mp hx
  rw [hZ, Subgroup.mem_bot] at hx'
  exact hx'

theorem iw_projZ_bijective {V H : Subgroup G} (hZ : Subgroup.center (Xbar V H) = ⊥) :
    Function.Bijective (projZ V H) :=
  ⟨iw_projZ_injective hZ, QuotientGroup.mk'_surjective _⟩

theorem iw_card_natural (n : ℕ) (F : Type) [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nat.card (Fin n ⊕ Fin n → F) = 2 ^ (2 * n) := by
  simp [Nat.card_fun, Nat.card_sum, Nat.card_eq_fintype_card, hF, two_mul]

theorem iw_relIndex [Finite G] {V H : Subgroup G} {K Q : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hKQ : K ≤ Q) (hKH : K ≤ H) (hQH : Q ≤ H)
    (hKW : K ⊓ wOf V H = Q ⊓ wOf V H) (hKb : Nat.card (barOf V H K) = 2)
    (hQb : Nat.card (barOf V H Q) = 2 ^ (2 * n - 1)) :
    K.relIndex Q = 2 ^ (2 * n - 2) := by
  have hpos : 0 < Nat.card ↥(Q ⊓ wOf V H) := Nat.card_pos
  have h1 := twb_card_barOf_mul (V := V) (H := H) (K := Q) hQH
  have h2 := twb_card_barOf_mul (V := V) (H := H) (K := K) hKH
  have h3 := Subgroup.relIndex_mul_card (H := K) (K := Q)
  rw [inf_eq_left.mpr hKQ] at h3
  rw [hKW, hKb] at h2
  rw [hQb] at h1
  have hp : (2 : ℕ) ^ (2 * n - 1) = 2 ^ (2 * n - 2) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 * Nat.card ↥(Q ⊓ wOf V H) by omega)
  calc K.relIndex Q * (2 * Nat.card ↥(Q ⊓ wOf V H))
      = K.relIndex Q * Nat.card ↥K := by rw [h2]
    _ = Nat.card ↥Q := h3
    _ = 2 ^ (2 * n - 1) * Nat.card ↥(Q ⊓ wOf V H) := h1.symm
    _ = 2 ^ (2 * n - 2) * (2 * Nat.card ↥(Q ⊓ wOf V H)) := by rw [hp]; ring

theorem iw_rtilde_eq {V H P : Subgroup G} {n : ℕ} {a : Fin n ⊕ Fin n → GaloisField 2 1}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 1))}
    {Φt : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H}
    (hP : Sec24bTilde V H P) (hbij : Function.Bijective Φt) (ha : a ≠ 0)
    (hT : CaseM.IsTransGroup a T) (hmap : T.map Φt = VZ V H) :
    Rtilde V H P = (spRad a).map Φt := by
  have hP' : Rtilde V H P = pCoreOf 2 (Subgroup.normalizer (VZ V H : Set (XbarZ V H))) := hP
  have hnorm : Subgroup.normalizer ((T.map Φt : Subgroup (XbarZ V H)) : Set (XbarZ V H)) =
      (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1)))).map Φt :=
    (Subgroup.map_normalizer_eq_of_bijective T hbij).symm
  have hpc : pCoreOf 2 ((Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1)))).map Φt) =
      (pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1))))).map Φt :=
    CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulEquiv.ofBijective Φt hbij)
      (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1))))
  have hcore : pCoreOf 2 (Subgroup.normalizer (T : Set (StatedSp n (GaloisField 2 1)))) =
      spRad a :=
    spCoreStmt_holds n (GaloisField 2 1) ha hT
  rw [hP', ← hmap, hnorm, hpc, hcore]

theorem iw_rbar_card (hB4 : SpRadFactsStatement) [Finite G] {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥) {n : ℕ} (hn : 2 ≤ n)
    (Φ : ↥(StatedSp n (GaloisField 2 1)) ≃* Xbar V H) {a : Fin n ⊕ Fin n → GaloisField 2 1}
    {T : Subgroup ↥(StatedSp n (GaloisField 2 1))} (ha : a ≠ 0)
    (hTa : CaseM.IsTransGroup a T) (hTΦ : T.map Φ.toMonoidHom = Vy V H) :
    Nat.card ↥(Rbar V H P) = 2 ^ (2 * n - 1) := by
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  set Φt : ↥(StatedSp n (GaloisField 2 1)) →* XbarZ V H := (projZ V H).comp Φ.toMonoidHom
    with hΦt
  have hΦtb : Function.Bijective Φt := (iw_projZ_bijective hZ).comp Φ.bijective
  have hΦT : T.map Φt = VZ V H := by
    rw [hΦt, ← Subgroup.map_map, hTΦ]
    rfl
  have hRt : Rtilde V H P = (spRad a).map Φt := iw_rtilde_eq hH.tilde hΦtb ha hTa hΦT
  have hRt_card : Nat.card ↥(Rtilde V H P) = 2 ^ (2 * n - 1) := by
    rw [hRt, Subgroup.card_map_of_injective hΦtb.1]
    exact (hB4 n (by omega) (GaloisField 2 1) hF2 a ha).2.2
  rw [← hRt_card]
  exact (Subgroup.card_map_of_injective (iw_projZ_injective hZ)).symm

theorem iw_cPbar_le [Finite G] {M V Q P H : Subgroup G} (hCP : CommPairingStatement)
    (hH : TwoEndHyp M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥) {n : ℕ} (hn : 2 ≤ n)
    (hPW : Nat.card ↥(P ⊓ wOf V H) = 2 ^ (2 * n - 1))
    (hRX : Nat.card ↥(barOf V H P ⊓ barOf V H (xOf V H)) = 2 ^ (2 * n - 1)) :
    cPbar V H P ≤ wOf V H := by
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hVH : V ≤ H := hc.V_le_H
  have hVP : V ≤ P := hc.V_le_P
  have hPH : P ≤ H := hc.PleH
  have hWX : wOf V H ≤ xOf V H := wOf_le_xOf V H
  have hVX : V ≤ xOf V H := le_xOf (V_mem_omegaOf V H)
  have hXH : xOf V H ≤ H := xOf_le_H hVH
  have hcPP : cPbar V H P ≤ P := inf_le_left
  have hcPcX : cPbar V H P ≤ cX V H := inf_le_right
  have hcPH : cPbar V H P ≤ H := hcPP.trans hPH
  have hWcX : wOf V H ≤ cX V H := twb_wOf_le_cX hVH
  have hXX : xOf V H ⊔ cPbar V H P = H := hH.concl.2.1
  have hIab : ∀ x ∈ wOf V H ⊔ cPbar V H P, ∀ y ∈ wOf V H ⊔ cPbar V H P, x * y = y * x :=
    fun x hx y hy => hH.concl.2.2.comm hx hy
  set I : Subgroup G := wOf V H ⊔ cPbar V H P with hI
  set A : Subgroup G := V ⊓ wOf V H with hA
  set Px : Subgroup G := P ⊓ xOf V H with hPx
  set K0 : Subgroup G := (P ⊓ wOf V H) ⊔ V with hK0
  set B : Subgroup G := I ⊓ P with hB
  have hWI : wOf V H ≤ I := le_sup_left
  have hcPI : cPbar V H P ≤ I := le_sup_right
  have hBP : B ≤ P := inf_le_right
  have hBI : B ≤ I := inf_le_left
  have hIcX : I ≤ cX V H := sup_le hWcX hcPcX
  have hPxP : Px ≤ P := inf_le_left
  have hPxX : Px ≤ xOf V H := inf_le_right
  have hPxH : Px ≤ H := hPxX.trans hXH
  have hK0P : K0 ≤ P := sup_le inf_le_left hVP
  have hK0H : K0 ≤ H := hK0P.trans hPH
  have hK0Px : K0 ≤ Px :=
    sup_le (le_inf inf_le_left (inf_le_right.trans hWX)) (le_inf hVP hVX)
  have hAB : A ≤ B := le_inf (inf_le_right.trans hWI) (inf_le_left.trans hVP)
  have hPWB : P ⊓ wOf V H ≤ B := le_inf (inf_le_right.trans hWI) inf_le_left
  have hPWK0 : P ⊓ wOf V H ≤ K0 := le_sup_left
  have hVK0 : V ≤ K0 := le_sup_right
  have hK0W : K0 ⊓ wOf V H = P ⊓ wOf V H :=
    le_antisymm (inf_le_inf hK0P le_rfl) (le_inf hPWK0 inf_le_right)
  have hPxW : Px ⊓ wOf V H = P ⊓ wOf V H := by
    rw [hPx, inf_assoc, inf_eq_right.mpr hWX]
  have hbarK0 : barOf V H K0 = barOf V H V := by
    rw [hK0, twb_barOf_sup (inf_le_left.trans hPH) hVH,
      twb_barOf_eq_bot (inf_le_right : P ⊓ wOf V H ≤ wOf V H), bot_sup_eq]
  have hKb : Nat.card ↥(barOf V H K0) = 2 := by
    rw [hbarK0]
    exact hH.q_two
  have hAcard : Nat.card ↥A = 2 := hH.module.trans hH.q_two
  have hbarPx : barOf V H Px = barOf V H P ⊓ barOf V H (xOf V H) := twb_barOf_inf_X
  have hQb : Nat.card ↥(barOf V H Px) = 2 ^ (2 * n - 1) := by
    rw [hbarPx]
    exact hRX
  have hn1 : 1 ≤ n := by omega
  have hrel : K0.relIndex Px = 2 ^ (2 * n - 2) :=
    iw_relIndex hn1 hK0Px hK0H hPxH (hK0W.trans hPxW.symm) hKb hQb
  have hcomm1 : ∀ b ∈ B, ∀ r ∈ Px, ⁅b, r⁆ ∈ A := by
    intro b hb r hr
    rw [hA]
    exact Subgroup.mem_inf.mpr ⟨hc.commutator_mem_V_of_mem_P (hBP hb) (hPxP hr),
      (hIcX (hBI hb)).2 r (hPxX hr)⟩
  have hcomm2 : ∀ a ∈ A, ∀ x ∈ B ⊔ Px, a * x = x * a := by
    intro a ha x hx
    have hxP : x ∈ P := (sup_le hBP hPxP) hx
    rw [hA] at ha
    exact hc.commute_of_mem_P hxP (Subgroup.mem_inf.mp ha).1
  have hcomm3 : ∀ b ∈ B, ∀ k ∈ K0, b * k = k * b := by
    intro b hb k hk
    have hbP : b ∈ P := hBP hb
    have hbI : b ∈ I := hBI hb
    have hle : K0 ≤ Subgroup.centralizer ({b} : Set G) := by
      refine sup_le ?_ ?_
      · intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff.mp hg]
        exact hIab b hbI w (hWI (Subgroup.mem_inf.mp hw).2)
      · intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff.mp hg]
        exact (hc.commute_of_mem_P hbP hv).symm
    exact Subgroup.mem_centralizer_iff.mp (hle hk) b (Set.mem_singleton b)
  have hcomm4 : ∀ b ∈ B, (∀ r ∈ Px, b * r = r * b) → b ∈ A := by
    intro b hb hbc
    have hbP : b ∈ P := hBP hb
    have hbI : b ∈ I := hBI hb
    have hbH : b ∈ H := hPH hbP
    have hbPc : b ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxS : x ∈ xOf V H ⊔ cPbar V H P := by
        rw [hXX]
        exact hPH hx
      have hN : ∀ h ∈ H, ∀ n ∈ xOf V H, h * n * h⁻¹ ∈ xOf V H := fun h hh n hn =>
        (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_xOf V H hh) n).mp hn
      obtain ⟨y, hy, c, hc', rfl⟩ := twb_mem_sup_mul hcPH hN hxS
      have hyP : y ∈ P := by
        have h := P.mul_mem hx (P.inv_mem (Subgroup.mem_inf.mp hc').1)
        simpa using h
      have hyPX : y ∈ Px := Subgroup.mem_inf.mpr ⟨hyP, hy⟩
      have h1 : b * y = y * b := hbc y hyPX
      have h2 : c * b = b * c := hIab c (hcPI hc') b hbI
      rw [mul_assoc, h2, ← mul_assoc, ← h1, mul_assoc]
    have hbV : b ∈ V := by
      have h := hbPc
      rw [hc.centralizer_P_eq] at h
      exact h
    have hbX : b ∈ xOf V H := hVX hbV
    have hbW : b ∈ wOf V H := by
      have hzc : (⟨piBar V H ⟨b, hbH⟩, mem_barOf_iff.mpr ⟨⟨b, hbH⟩, hbX, rfl⟩⟩ : Xbar V H) ∈
          Subgroup.center (Xbar V H) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨x, hxX, hxg⟩ := mem_barOf_iff.mp g.2
        have hW : ((⁅(⟨b, hbH⟩ : ↥H), x⁆ : ↥H) : G) ∈ wOf V H := (hIcX hbI).2 x hxX
        have h1 : piBar V H ⁅(⟨b, hbH⟩ : ↥H), x⁆ = 1 := (piBar_eq_one_iff _).mpr hW
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
        apply Subtype.ext
        show (g : Hbar V H) * piBar V H ⟨b, hbH⟩ = piBar V H ⟨b, hbH⟩ * (g : Hbar V H)
        rw [← hxg]
        exact h1.symm
      rw [hZ, Subgroup.mem_bot] at hzc
      have h2 : piBar V H ⟨b, hbH⟩ = 1 := congrArg Subtype.val hzc
      exact (piBar_eq_one_iff _).mp h2
    rw [hA]
    exact Subgroup.mem_inf.mpr ⟨hbV, hbW⟩
  have hconj : ∀ r ∈ Px, ∀ k ∈ K0, r * k * r⁻¹ ∈ K0 := by
    intro r hr k hk
    have hrP : r ∈ P := hPxP hr
    have hrH : r ∈ H := hPH hrP
    have hle : K0 ≤ K0.comap (MulAut.conj r).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro w hw
        rw [Subgroup.mem_comap]
        change r * w * r⁻¹ ∈ K0
        obtain ⟨hwP, hwW⟩ := Subgroup.mem_inf.mp hw
        exact hPWK0 (Subgroup.mem_inf.mpr ⟨P.mul_mem (P.mul_mem hrP hwP) (P.inv_mem hrP),
          (Subgroup.mem_normalizer_iff.mp (H_le_normalizer_wOf V H hrH) w).mp hwW⟩)
      · intro v hv
        rw [Subgroup.mem_comap]
        change r * v * r⁻¹ ∈ K0
        have hrv : r * v = v * r := (hc.commute_of_mem_P hrP hv).symm
        rw [hrv, mul_inv_cancel_right]
        exact hVK0 hv
    have h := hle hk
    rw [Subgroup.mem_comap] at h
    exact h
  have hcomm5 : ∀ r ∈ Px, ∀ r' ∈ Px, ⁅r, r'⁆ ∈ K0 := fun r hr r' hr' =>
    hVK0 (hc.commutator_mem_V_of_mem_P (hPxP hr) (hPxP hr'))
  have hsq : ∀ r ∈ Px, r * r ∈ K0 := fun r hr => hVK0 (twb_mul_self_mem_V hc (hPxP hr))
  have hcP := hCP G A B Px K0 (2 * n - 2) hAB hK0Px hcomm1 hcomm2 hcomm3 hcomm4 hconj hcomm5
    hsq hrel
  rw [hAcard] at hcP
  have hpow : (2 : ℕ) * 2 ^ (2 * n - 2) = 2 ^ (2 * n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hcard : Nat.card ↥B ≤ Nat.card ↥(P ⊓ wOf V H) := by
    rw [hPW, ← hpow]
    exact hcP
  have heq : P ⊓ wOf V H = B := Subgroup.eq_of_le_of_card_ge hPWB hcard
  calc cPbar V H P ≤ B := le_inf hcPI hcPP
    _ = P ⊓ wOf V H := heq.symm
    _ ≤ wOf V H := inf_le_right

theorem sec34IW_holds (hN : NaturalModuleStatement) (hB4 : SpRadFactsStatement)
    (hCP : CommPairingStatement) : Sec34IWStatement := by
  intro G _ _ M V Q P H hH hZ
  obtain ⟨n, Φ, ψ, hn2, -, ⟨a, T, ha, hTa, hTΦ⟩, -⟩ := hN G M V Q P H hH hZ
  have hF2 : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero, pow_one]
  have hWcard : Nat.card ↥(wOf V H) = 2 ^ (2 * n) := by
    rw [← iw_card_natural n (GaloisField 2 1) hF2]
    exact (Nat.card_congr ψ.toEquiv).symm
  have hsplit := twistedWSplit_holds G M V Q P H hH.setup hH.concl
  rw [hH.module, hH.q_two, hWcard] at hsplit
  have hPW : Nat.card ↥(P ⊓ wOf V H) = 2 ^ (2 * n - 1) := by
    have hp : (2 : ℕ) ^ (2 * n) = 2 ^ (2 * n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
    rw [← hsplit]
    exact hp
  have hRbar := iw_rbar_card hB4 hH hZ hn2 Φ ha hTa hTΦ
  have hRmap : (Rbar V H P).map (barOf V H (xOf V H)).subtype =
      barOf V H P ⊓ barOf V H (xOf V H) := by
    unfold Rbar
    exact Subgroup.subgroupOf_map_subtype _ _
  have hRX : Nat.card ↥(barOf V H P ⊓ barOf V H (xOf V H)) = 2 ^ (2 * n - 1) := by
    rw [← hRmap, Subgroup.card_map_of_injective (barOf V H (xOf V H)).subtype_injective, hRbar]
  exact iw_cPbar_le hCP hH hZ hn2 hPW hRX

end CFSG.RankThree.GF2n.Tim79a
