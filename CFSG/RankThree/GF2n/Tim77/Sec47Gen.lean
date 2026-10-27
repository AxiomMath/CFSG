module

public import CFSG.RankThree.GF2n.Tim77.Defs
public import CFSG.StronglyEmbedded.PSL2Facts
public import CFSG.RankThree.GF2n.Tim77.AutDichU3
public import CFSG.RankThree.S4Free.Stellmacher24Sz
public import CFSG.LieType.SuzukiSubgroups.Main
public import CFSG.Quasithin.Vol2.Ch11SecE3Sz

public section

namespace CFSG.RankThree.GF2n.Tim77

private theorem sec47g_comm {X : Type} [Group X] {Z : Subgroup X}
    (hZ : CFSG.Open.IsElemAbelian 2 Z) {x y : X} (hx : x ∈ Z) (hy : y ∈ Z) :
    x * y = y * x :=
  congrArg Subtype.val (hZ.1.is_comm.comm (⟨x, hx⟩ : ↥Z) ⟨y, hy⟩)

private theorem sec47g_le {X : Type} [Group X] {Z E : Subgroup X}
    (hZ : CFSG.Open.IsElemAbelian 2 Z) (hEZ : E ≤ Z) : CFSG.Open.IsElemAbelian 2 E :=
  ⟨⟨⟨fun x y => Subtype.ext (sec47g_comm hZ (hEZ x.2) (hEZ y.2))⟩⟩,
    fun x hx => hZ.2 x (hEZ hx)⟩

private theorem sec47g_comap {X Y : Type} [Group X] [Group Y] {Z : Subgroup Y} {f : X →* Y}
    (hf : Function.Injective f) (hZ : CFSG.Open.IsElemAbelian 2 Z) :
    CFSG.Open.IsElemAbelian 2 (Z.comap f) := by
  refine ⟨⟨⟨fun x y => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · simp only [Subgroup.coe_mul, map_mul]
    exact sec47g_comm hZ (Subgroup.mem_comap.mp x.2) (Subgroup.mem_comap.mp y.2)
  · rw [map_pow, map_one]
    exact hZ.2 _ (Subgroup.mem_comap.mp hx)

theorem sec47_gen_psl2 {L : Type} [Group L] [Finite L] {f : ℕ} (hf : 2 ≤ f)
    (hL : IsPSL2Model L f) {a g : L} (ha : orderOf a = 2) (hg : orderOf g = 2)
    (hag : ¬ Commute a g) :
    Subgroup.closure ({x : L | x * x = 1 ∧ Commute x a} ∪ {g}) = ⊤ := by
  classical
  obtain ⟨e⟩ := hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf0 : f ≠ 0 := by omega
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact absurd ha (by norm_num)
  have ha2 : a * a = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  obtain ⟨S, haS⟩ : ∃ S : Sylow 2 L, a ∈ (S : Subgroup L) := by
    have hPa : IsPGroup 2 (Subgroup.zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
    obtain ⟨S, hS⟩ := hPa.exists_le_sylow
    exact ⟨S, hS (Subgroup.mem_zpowers a)⟩
  have hC : Subgroup.centralizer ({a} : Set L) = (S : Subgroup L) :=
    CFSG.BenderSuzuki.psl2_centralizer_eq_sylow e hf haS ha1
  have hScomm : ∀ s ∈ (S : Subgroup L), s * a = a * s := fun s hs => by
    have h : s ∈ Subgroup.centralizer ({a} : Set L) := by
      rw [hC]
      exact hs
    exact Subgroup.mem_centralizer_singleton_iff.mp h
  have hSab : CFSG.Open.IsElemAbelian 2 (S : Subgroup L) :=
    (CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow hf0 ⟨e⟩ S).isElemAbelian
  obtain ⟨H, hH⟩ : ∃ H : Subgroup L,
      H = Subgroup.closure ({x : L | x * x = 1 ∧ Commute x a} ∪ {g}) := ⟨_, rfl⟩
  rw [← hH]
  have hTH : ∀ x : L, x * x = 1 → Commute x a → x ∈ H := fun x h1 h2 => by
    rw [hH]
    exact Subgroup.subset_closure (Or.inl ⟨h1, h2⟩)
  have hgH : g ∈ H := by
    rw [hH]
    exact Subgroup.subset_closure (Or.inr rfl)
  have hSH : ∀ s ∈ (S : Subgroup L), s ∈ H := fun s hs =>
    hTH s (by rw [← sq]; exact hSab.2 s hs) (hScomm s hs)
  have hS'H : ∀ x ∈ ((g • S : Sylow 2 L) : Subgroup L), x ∈ H := by
    intro x hx
    rw [CFSG.CGT.T75B.mem_smul_sylow] at hx
    have hxe : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    rw [hxe]
    exact H.mul_mem (H.mul_mem hgH (hSH _ hx)) (H.inv_mem hgH)
  have hne : (S : Sylow 2 L) ≠ g • S := by
    intro hEq
    have hgN : g ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) :=
      Sylow.smul_eq_iff_mem_normalizer.mp hEq.symm
    have hgS : g ∈ (S : Subgroup L) := involution_mem_sylow_of_normalizer S hg hgN
    exact hag (hScomm g hgS).symm
  have hsup := CFSG.BenderSuzuki.psl2_sup_sylow_eq_top e hf hne
  rw [eq_top_iff, ← hsup]
  exact sup_le (fun s hs => hSH s hs) (fun x hx => hS'H x hx)

theorem sec47_gen_sz {L : Type}
    [Group L] [Finite L] {k : ℕ} (hk : 1 ≤ k) (hL : IsSzModel L k) {a g : L}
    (ha : orderOf a = 2) (hg : orderOf g = 2) (hag : ¬ Commute a g) :
    Subgroup.closure ({x : L | x * x = 1 ∧ Commute x a} ∪ {g}) = ⊤ := by
  classical
  obtain ⟨e⟩ := hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * k + 1)) = 2 ^ (2 * k + 1) :=
    GaloisField.card 2 (2 * k + 1) (by omega)
  let e2 := e.trans
    (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup k).some
  have hH : CFSG.Quasithin.IsSz (2 * k + 1) L :=
    CFSG.LieType.SuzukiSubgroups.isSz_of_mulEquiv hk e
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact absurd ha (by norm_num)
  have ha2 : a * a = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one a
    rwa [ha] at this
  obtain ⟨S, haS⟩ : ∃ S : Sylow 2 L, a ∈ (S : Subgroup L) := by
    have hPa : IsPGroup 2 (Subgroup.zpowers a) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
    obtain ⟨S, hS⟩ := hPa.exists_le_sylow
    exact ⟨S, hS (Subgroup.mem_zpowers a)⟩
  have hC : Subgroup.centralizer ({a} : Set L) = (S : Subgroup L) :=
    CFSG.RankThree.S4Free.Suzuki.centralizer_eq_sylow_of_mulEquiv hK e2 S ha haS
  have hScomm : ∀ s ∈ (S : Subgroup L), s * a = a * s := fun s hs => by
    have h : s ∈ Subgroup.centralizer ({a} : Set L) := by
      rw [hC]
      exact hs
    exact Subgroup.mem_centralizer_singleton_iff.mp h
  obtain ⟨φ, hSφ, -⟩ := CFSG.RankThree.S4Free.Suzuki.exists_mulEquiv_sylow_eq hK e2 S
  have hZeq := CFSG.RankThree.S4Free.Suzuki.inf_centralizer_eq_comap hk hK φ hSφ
  have hZcard := (CFSG.RankThree.S4Free.Suzuki.card_sylow_and_center hk hK e2 S).2.1
  have hZ0 := CFSG.ShultStronglyClosedTI.SuzukiModel.isElemAbelian_suzukiZ0 hK
  obtain ⟨Zs, hZsdef⟩ : ∃ Zs : Subgroup L,
      Zs = (S : Subgroup L) ⊓ Subgroup.centralizer ((S : Subgroup L) : Set L) := ⟨_, rfl⟩
  have hZsab : CFSG.Open.IsElemAbelian 2 Zs := by
    rw [hZsdef, hZeq]
    exact sec47g_comap φ.injective hZ0
  have hZscard : Nat.card Zs = 2 ^ (2 * k + 1) := by
    rw [hZsdef]
    exact hZcard
  have hZscomm : ∀ z ∈ Zs, z * a = a * z := fun z hz => by
    rw [hZsdef] at hz
    exact hScomm z hz.1
  have hZssq : ∀ z ∈ Zs, z * z = 1 := fun z hz => by
    rw [← sq]
    exact hZsab.2 z hz
  obtain ⟨U, hUdef⟩ : ∃ U : Subgroup L,
      U = Subgroup.closure ({x : L | x * x = 1 ∧ Commute x a} ∪ {g}) := ⟨_, rfl⟩
  rw [← hUdef]
  have hTU : ∀ x : L, x * x = 1 → Commute x a → x ∈ U := fun x h1 h2 => by
    rw [hUdef]
    exact Subgroup.subset_closure (Or.inl ⟨h1, h2⟩)
  have hgU : g ∈ U := by
    rw [hUdef]
    exact Subgroup.subset_closure (Or.inr rfl)
  have haU : a ∈ U := hTU a ha2 (Commute.refl a)
  have hZU : Zs ≤ U := fun z hz => hTU z (hZssq z hz) (hZscomm z hz)
  by_contra hU
  have hZdvd : 2 ^ 2 ∣ Nat.card ↥Zs := by
    rw [hZscard]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Zs) 2 hZdvd
  have hEZs : F.map Zs.subtype ≤ Zs := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hE4 : Nat.card (F.map Zs.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective, hF]
    norm_num
  have hEel : CFSG.Open.IsElemAbelian 2 (F.map Zs.subtype) := sec47g_le hZsab hEZs
  have hEU : F.map Zs.subtype ≤ U := hEZs.trans hZU
  rcases CFSG.LieType.SuzukiSubgroups.le_normalizer_or_isSz hH hU hEU hEel hE4 with
    ⟨Q, hQN⟩ | ⟨j, hjdvd, hjlt, hjU⟩
  ·
    have haQ : a ∈ (Q : Subgroup L) := involution_mem_sylow_of_normalizer Q ha (hQN haU)
    have hcj : g * a * g⁻¹ ∈ U := U.mul_mem (U.mul_mem hgU haU) (U.inv_mem hgU)
    have hcj2 : (g * a * g⁻¹) * (g * a * g⁻¹) = 1 := by
      have e1 : (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      rw [e1, ha2, mul_one, mul_inv_cancel]
    have hcj1 : g * a * g⁻¹ ≠ 1 := by
      intro h
      apply ha1
      have e1 : a = g⁻¹ * (g * a * g⁻¹) * g := by group
      rw [e1, h]
      group
    have hcjord : orderOf (g * a * g⁻¹) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hcj2) hcj1
    have hcjQ : g * a * g⁻¹ ∈ (Q : Subgroup L) :=
      involution_mem_sylow_of_normalizer Q hcjord (hQN hcj)
    have hcjS : g * a * g⁻¹ ∈ ((g • S : Sylow 2 L) : Subgroup L) := by
      rw [CFSG.CGT.T75B.mem_smul_sylow]
      have e1 : g⁻¹ * (g * a * g⁻¹) * g = a := by group
      rw [e1]
      exact haS
    have hQS : Q = S := CFSG.RankThree.S4Free.Suzuki.eq_of_le_inf_sylow hK e2
      (P := Subgroup.zpowers a) (fun h => ha1 (Subgroup.zpowers_eq_bot.mp h))
      (Subgroup.zpowers_le.mpr haQ) (Subgroup.zpowers_le.mpr haS)
    have hQgS : Q = g • S := CFSG.RankThree.S4Free.Suzuki.eq_of_le_inf_sylow hK e2
      (P := Subgroup.zpowers (g * a * g⁻¹)) (fun h => hcj1 (Subgroup.zpowers_eq_bot.mp h))
      (Subgroup.zpowers_le.mpr hcjQ) (Subgroup.zpowers_le.mpr hcjS)
    have hSgS : g • S = S := hQgS.symm.trans hQS
    have hgN : g ∈ Subgroup.normalizer ((S : Subgroup L) : Set L) :=
      Sylow.smul_eq_iff_mem_normalizer.mp hSgS
    have hgS : g ∈ (S : Subgroup L) := involution_mem_sylow_of_normalizer S hg hgN
    exact hag (hScomm g hgS).symm
  ·
    obtain ⟨-, b, hb, K', hK'f, hK'fin, hjb, hcard', ⟨e'⟩⟩ := hjU
    subst hjb
    have hsub : CFSG.Open.IsElemAbelian 2 (Zs.subgroupOf U) :=
      sec47g_comap (f := U.subtype) Subtype.val_injective hZsab
    have hA : CFSG.Open.IsElemAbelian 2 ((Zs.subgroupOf U).map e'.toMonoidHom) :=
      CFSG.RankThree.S4Free.Stell.isElemAbelian_map hsub e'.toMonoidHom
    have hbound := CFSG.Quasithin.Vol2.Ch11.SecE3.card_le_of_isElemAbelian_suzuki hcard' hA
    have hcardA : Nat.card ((Zs.subgroupOf U).map e'.toMonoidHom) = 2 ^ (2 * k + 1) := by
      rw [Subgroup.card_map_of_injective e'.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv, hZscard]
    rw [hcardA, hcard'] at hbound
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hbound
    omega

end CFSG.RankThree.GF2n.Tim77

end
