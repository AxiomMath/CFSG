module

public import CFSG.Quasithin.H13.GoldschmidtU43ENorm6
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm3
public import CFSG.Quasithin.H13.GoldschmidtU43ENorm5

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)

theorem not_hasNormalPComplement_Nbar : ¬ CFSG.HasNormalPComplement 2 S.Nbar := by
  rintro ⟨N₁, hN₁, hcop, hpg⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set MK : Subgroup ↥S.Ng := S.Mg.subgroupOf S.Ng with hMK
  set π : ↥S.Ng →* S.Nbar := QuotientGroup.mk' MK with hπ
  have hodd : Odd (Nat.card N₁) := Nat.coprime_two_left.mp hcop
  have hle : N₁ ≤ CFSG.oddCore S.Nbar :=
    CFSG.BrauerSuzuki.Helpers.normal_odd_le_oddCore N₁ hN₁ hodd
  rw [S.oddCore_Nbar] at hle
  have hbot : N₁ = ⊥ := le_bot_iff.mp hle
  have hN2 : ∀ x : S.Nbar, ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
    intro x
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hpg) (QuotientGroup.mk x)
    refine ⟨k, ?_⟩
    have h1 : (QuotientGroup.mk x : S.Nbar ⧸ N₁) ^ (2 ^ k) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hbot, Subgroup.mem_bot] at h1
    exact h1
  have h3M : ∀ x : ↥S.Ng, ∀ j : ℕ, x ^ (3 ^ j) = 1 → x ∈ MK := by
    intro x j hj
    obtain ⟨k, hk⟩ := hN2 (π x)
    have h2 : (π x) ^ (2 ^ k) = 1 := hk
    have h3 : (π x) ^ (3 ^ j) = 1 := by rw [← map_pow, hj, map_one]
    have hcop23 : Nat.Coprime (2 ^ k) (3 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
    have hord : orderOf (π x) = 1 := by
      have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
      rw [hcop23.gcd_eq_one] at this
      exact Nat.dvd_one.mp this
    exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp hord)
  have hmax : ∀ Q : Subgroup G, IsPGroup 3 Q → S.Mg ≤ Q → Q = S.Mg := by
    intro Q hQ hMQ
    by_contra hne
    have hlt : S.Mg.subgroupOf Q < ⊤ := by
      refine lt_top_iff_ne_top.mpr (fun htop => hne ?_)
      refine le_antisymm (fun q hq => ?_) hMQ
      have : (⟨q, hq⟩ : ↥Q) ∈ S.Mg.subgroupOf Q := by
        rw [htop]
        trivial
      exact this
    have : Group.IsNilpotent ↥Q := hQ.isNilpotent
    have hnc : NormalizerCondition ↥Q := Group.normalizerCondition_of_isNilpotent
    obtain ⟨x, hxN, hxn⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
    have hxNg : (x : G) ∈ S.Ng := by
      have : x ∈ (Subgroup.normalizer (S.Mg : Set G)).subgroupOf Q := by
        rw [Subgroup.subgroupOf_normalizer_eq hMQ]
        exact hxN
      exact Subgroup.mem_subgroupOf.mp this
    obtain ⟨j, hj⟩ := hQ x
    have hxj : (⟨(x : G), hxNg⟩ : ↥S.Ng) ^ (3 ^ j) = 1 := Subtype.ext (by
      have := congrArg Subtype.val hj
      simpa using this)
    exact hxn (h3M _ j hxj)
  obtain ⟨P2, hP2⟩ := S.exists_sylow_Dg
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective MK
  set Pbar : Sylow 2 S.Nbar := P2.mapSurjective hsurj with hPbar
  have hTop : IsPGroup 2 (⊤ : Subgroup S.Nbar) := fun g => by
    obtain ⟨k, hk⟩ := hN2 g
    exact ⟨k, Subtype.ext hk⟩
  have hPtop : (⊤ : Subgroup S.Nbar) = (Pbar : Subgroup S.Nbar) :=
    Pbar.is_maximal' hTop le_top
  have hNdm : ∀ n : ↥S.Ng, ∃ d ∈ S.Dg, ∃ m ∈ S.Mg, (n : G) = d * m := by
    intro n
    have hmem : π n ∈ (Pbar : Subgroup S.Nbar) := by
      rw [← hPtop]
      trivial
    rw [hPbar, Sylow.coe_mapSurjective, hP2] at hmem
    obtain ⟨d, hd, hdn⟩ := hmem
    have hdm : d⁻¹ * n ∈ MK := by
      have e : π (d⁻¹ * n) = 1 := by
        rw [map_mul, map_inv, hdn]
        group
      exact (QuotientGroup.eq_one_iff _).mp e
    refine ⟨(d : G), hd, ((d⁻¹ * n : ↥S.Ng) : G), hdm, ?_⟩
    simp
  have hM3 : IsPGroup 3 S.Mg := IsPGroup.of_card (n := 4) (by rw [S.card_Mg_eq_81]; norm_num)
  obtain ⟨P3, hP3⟩ := hM3.exists_le_sylow
  have hP3eq : (P3 : Subgroup G) = S.Mg := hmax _ P3.isPGroup' hP3
  have hset : (P3 : Set G) = (S.Mg : Set G) := Set.ext fun x => SetLike.ext_iff.mp hP3eq x
  have hcomm : IsMulCommutative (P3 : Subgroup G) := ⟨⟨fun a b => Subtype.ext (by
    have ha : (a : G) ∈ S.Mg := hP3eq ▸ a.2
    have hb : (b : G) ∈ S.Mg := hP3eq ▸ b.2
    exact S.abelian_Mg _ ha _ hb)⟩⟩
  obtain ⟨g, hg⟩ := S.exists_conj_T_T1
  have hfuse : ∀ t ∈ S.Tg, g * t * g⁻¹ ∈ S.Tg := by
    intro t ht
    have hT1 : g * t * g⁻¹ ∈ S.T1 := hg t ht
    have hx : g * t * g⁻¹ ∈ (P3 : Subgroup G) := by
      rw [hP3eq]
      exact S.T1_le_Mg hT1
    have hconj : g⁻¹ * (g * t * g⁻¹) * g = t := by group
    have hy : g⁻¹ * (g * t * g⁻¹) * g ∈ (P3 : Subgroup G) := by
      rw [hconj, hP3eq]
      exact S.Tg_le_Mg ht
    obtain ⟨n, hn, hneq⟩ := Sylow.conj_eq_normalizer_conj_of_mem P3 (g * t * g⁻¹) g hx hy
    have hnN : n ∈ S.Ng := by
      rw [hset] at hn
      exact hn
    obtain ⟨d, hd, m, hm, hdm⟩ := hNdm ⟨n, hnN⟩
    have hdm' : n = d * m := hdm
    have e1 : g * t * g⁻¹ = n * t * n⁻¹ := by
      have h1 : t = n⁻¹ * (g * t * g⁻¹) * n := by rw [← hneq, hconj]
      calc g * t * g⁻¹ = n * (n⁻¹ * (g * t * g⁻¹) * n) * n⁻¹ := by group
        _ = n * t * n⁻¹ := by rw [← h1]
    have hmt : m * t = t * m := S.abelian_Mg m hm t (S.Tg_le_Mg ht)
    have e2 : n * t * n⁻¹ = d * t * d⁻¹ := by
      rw [hdm']
      calc d * m * t * (d * m)⁻¹ = d * (m * t) * m⁻¹ * d⁻¹ := by group
        _ = d * (t * m) * m⁻¹ * d⁻¹ := by rw [hmt]
        _ = d * t * d⁻¹ := by group
    rw [e1, e2]
    exact (Subgroup.mem_normalizer_iff.mp (S.Dg_le_normalizer_Tg hd) t).mp ht
  have hsub : S.Tg.map (MulAut.conj g).toMonoidHom ≤
      S.Tg ⊓ Subgroup.centralizer ({(S.u : G)} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hfuse t ht, (hg t ht).2⟩
  have h9 : Nat.card (S.Tg.map (MulAut.conj g).toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, S.card_Tg]
  have hle9 := Subgroup.card_le_of_le hsub
  rw [h9, S.card_Tg_inf_u] at hle9
  omega

end JWSetup

end CFSG.Quasithin.H13.U43
