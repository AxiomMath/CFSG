module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
public import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem thetaComponentsAt_inv_eq {G : Type} [Group G] (c : G) :
    thetaComponentsAt 3 c⁻¹ = thetaComponentsAt 3 c := by
  have h : Subgroup.centralizer ({c⁻¹} : Set G) = Subgroup.centralizer {c} := by
    ext z
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff (a := z) (b := c)
  unfold thetaComponentsAt
  rw [h]

theorem sq_centralizes_of_invData {G : Type} [Group G] [Finite G] {E EY Y : Subgroup G}
    {b c t : G} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) (hbE : b ∈ E)
    (hd : InvData E b c Y t EY) : ∀ x ∈ E, t * t * x * (t * t)⁻¹ = x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hb1 : b ≠ 1 := fun h => hd.not_mem_b (h ▸ one_mem _)
  have hbo : orderOf b = 3 := orderOf_eq_prime (hEe.2 b hbE) hb1
  have hBcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hbo]
  have hBE : Subgroup.zpowers b ≤ E := Subgroup.zpowers_le.mpr hbE
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ EY, x * y = y * x := fun x hx y hy =>
    hEcomm x (hBE hx) y (hd.le_E hy)
  obtain ⟨hcardeq, hset⟩ :=
    CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers b) EY hcomm
  have hinf : Nat.card (Subgroup.zpowers b ⊓ EY : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers b ⊓ EY : Subgroup G) ∣ 3 := by
      rw [← hBcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have heq : Subgroup.zpowers b ⊓ EY = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hBcard])
      exact hd.not_mem_b (inf_eq_left.mp heq (Subgroup.mem_zpowers b))
  have hsup : Nat.card (Subgroup.zpowers b ⊔ EY : Subgroup G) = 27 := by
    rw [hinf, hBcard, hd.card_EY] at hcardeq
    omega
  have hsupE : Subgroup.zpowers b ⊔ EY = E :=
    Subgroup.eq_of_le_of_card_ge (sup_le hBE hd.le_E) (by rw [hsup, hE27])
  intro x hx
  have hxmem : x ∈ ((Subgroup.zpowers b ⊔ EY : Subgroup G) : Set G) := by rw [hsupE]; exact hx
  rw [hset] at hxmem
  obtain ⟨u, hu, y, hy, hxy⟩ := hxmem
  have hxy : u * y = x := hxy
  have hu' : u ∈ Subgroup.zpowers b := hu
  have hy' : y ∈ EY := hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
  subst hxy
  have hb2 : t * t * b * (t * t)⁻¹ = b := by
    have h0 : t * b = b * t := hd.comm_b
    calc t * t * b * (t * t)⁻¹ = t * (t * b) * t⁻¹ * t⁻¹ := by group
      _ = t * (b * t) * t⁻¹ * t⁻¹ := by rw [h0]
      _ = (t * b) * t * t⁻¹ * t⁻¹ := by group
      _ = (b * t) * t * t⁻¹ * t⁻¹ := by rw [h0]
      _ = b := by group
  have hy2 : t * t * y * (t * t)⁻¹ = y := by
    have h1 := hd.inv y hy'
    have h2 := hd.inv y⁻¹ (inv_mem hy')
    calc t * t * y * (t * t)⁻¹ = t * (t * y * t⁻¹) * t⁻¹ := by group
      _ = t * y⁻¹ * t⁻¹ := by rw [h1]
      _ = y := by rw [h2, inv_inv]
  have hbk : t * t * b ^ k * (t * t)⁻¹ = b ^ k := by
    have h := map_zpow (MulAut.conj (t * t)) b k
    simp only [MulAut.conj_apply] at h
    rw [hb2] at h
    exact h
  calc t * t * (b ^ k * y) * (t * t)⁻¹
      = (t * t * b ^ k * (t * t)⁻¹) * (t * t * y * (t * t)⁻¹) := by group
    _ = b ^ k * y := by rw [hbk, hy2]

theorem s2swap_holds : S2swap := by
  intro G _ _ A c L E F a b R Y hY t EY hd htL
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hD, hSL2, -, hEle, hEe, hE27, hEC, hEL, -⟩ := hY.hCfg
  have hcL : c ∈ L := mem_of_isSLThreePiTwo slTwoCenter hD hSL2
  have hSL : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) :=
    ResProof.isSLThreePi_of_isSLThreePiTwo hD hSL2
  have hty : Item131bProof.HeisType (L ⧸ aschbacherSolvableCore 3 L) := Or.inl hSL
  obtain ⟨hcE, hP1, hP2, hsup⟩ :=
    Item131bProof.e_facts hD hty hcL (hEle.trans inf_le_left) hEe hE27 hEC hEL
  have hL := hD.mem_thetaComponentsAt
  have hELN : E ≤ Subgroup.normalizer (L : Set G) :=
    (hEle.trans inf_le_left).trans (sup_le Subgroup.le_normalizer hD.le_normalizer)
  have htc : t * c * t⁻¹ = c⁻¹ := hd.inv c hd.mem_c
  have hL' : L.map (MulAut.conj t).toMonoidHom ∈ thetaComponentsAt 3 c := by
    have h := map_mem_thetaComponentsAt (MulAut.conj t) hL
    have hc' : (MulAut.conj t) c = c⁻¹ := by rw [MulAut.conj_apply, htc]
    rw [hc', thetaComponentsAt_inv_eq] at h
    exact h
  have hne : L.map (MulAut.conj t).toMonoidHom ≠ L := fun h =>
    htL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have h3 : ∀ x ∈ E ⊓ L, t * x * t⁻¹ ∈ E ⊓ Sec4.thetaQuotCentralizer L := by
    intro x hx
    have hxE : t * x * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hd.mem_normalizer x).mp hx.1
    have hxL' : t * x * t⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx.2, by simp [MulAut.conj_apply]⟩
    exact Subgroup.mem_inf.mpr ⟨hxE,
      Sec13.mem_thetaQuotCentralizer_of_ne_mem_thetaComponentsAt hL' hL hne hxL' (hELN hxE)⟩
  have hsurj : ∀ y ∈ E ⊓ Sec4.thetaQuotCentralizer L, t⁻¹ * y * t ∈ E ⊓ L := by
    set f : ↥(E ⊓ L) → ↥(E ⊓ Sec4.thetaQuotCentralizer L) :=
      fun x => ⟨t * (x : G) * t⁻¹, h3 x x.2⟩ with hf
    have hinj : Function.Injective f := by
      intro x x' h
      have h' : t * (x : G) * t⁻¹ = t * (x' : G) * t⁻¹ := congrArg Subtype.val h
      exact Subtype.ext (by simpa using h')
    have hbij : Function.Bijective f :=
      hinj.bijective_of_nat_card_le (by rw [hP1, hP2])
    intro y hy
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
    have hx' : t * (x : G) * t⁻¹ = y := congrArg Subtype.val hx
    have : t⁻¹ * y * t = (x : G) := by rw [← hx']; group
    rw [this]
    exact x.2
  have hb := hY.hbE
  have hsq := sq_centralizes_of_invData hEe hE27 hb hd
  have hswap : ∀ y ∈ E, t * y * t⁻¹ = t⁻¹ * y * t := by
    intro y hy
    have h := hsq y hy
    calc t * y * t⁻¹ = t⁻¹ * (t * t * y * (t * t)⁻¹) * t := by group
      _ = t⁻¹ * y * t := by rw [h]
  refine ⟨hL', hne, h3, ?_, hsurj⟩
  intro y hy
  rw [hswap y hy.1]
  exact hsurj y hy

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
