module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7Spec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3A7K2A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16t3_exists_mul_of_mem_sup {M YL YK : Subgroup G}
    (hYLM : (YL.subgroupOf M).Normal) (hYLM' : YL ≤ M) (hYKM' : YK ≤ M) {x : G}
    (hx : x ∈ YL ⊔ YK) : ∃ y ∈ YL, ∃ k ∈ YK, y * k = x := by
  have hxM : x ∈ M := (sup_le hYLM' hYKM') hx
  haveI : (YL.subgroupOf M).Normal := hYLM
  have hx' : (⟨x, hxM⟩ : ↥M) ∈ (YL.subgroupOf M) ⊔ (YK.subgroupOf M) := by
    rw [← Subgroup.subgroupOf_sup hYLM' hYKM']
    exact hx
  obtain ⟨y, hy, k, hk, hyk⟩ := (Subgroup.mem_sup_of_normal_left (s := YL.subgroupOf M)
    (t := YK.subgroupOf M)).1 hx'
  exact ⟨y.1, hy, k.1, hk, by simpa using congrArg Subtype.val hyk⟩

private theorem s16t3_prime_dvd_card_of_sup_of_normal {A : Type*} [Group A] [Finite A]
    {N P H : Subgroup A} [N.Normal] (hsup : N ⊔ P = ⊤)
    (hN : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(N ⊓ H) → q = 2 ∨ q = 3)
    (hP : IsPGroup 2 ↥P) {q : ℕ} (hq : q.Prime) (hqH : q ∣ Nat.card ↥H) : q = 2 ∨ q = 3 := by
  by_cases hq2 : q = 2
  · exact Or.inl hq2
  · right
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' q (G := ↥H) hqH
    have hxsup : (x : A) ∈ N ⊔ P := by rw [hsup]; exact Subgroup.mem_top _
    obtain ⟨n, hn, p, hp, hx⟩ := (Subgroup.mem_sup_of_normal_left (s := N) (t := P)).1 hxsup
    obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
    have hpk : p ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hxN : (x : A) ^ 2 ^ k ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      show (QuotientGroup.mk' N) ((x : A) ^ 2 ^ k) = 1
      have hn1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_pow, ← hx, map_mul, hn1, one_mul, ← map_pow, hpk, map_one]
    have hxNH : (x : A) ^ 2 ^ k ∈ N ⊓ H := ⟨hxN, pow_mem x.2 _⟩
    have hx2_order : orderOf ((x : A) ^ 2 ^ k) = q := by
      rw [orderOf_pow, orderOf_coe, hxord]
      have hcop : Nat.Coprime q (2 ^ k) :=
        Nat.Coprime.pow_right k ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
      rw [hcop.gcd_eq_one, Nat.div_one]
    have hq_dvd : q ∣ Nat.card ↥(N ⊓ H) := by
      have hord : orderOf (⟨(x : A) ^ 2 ^ k, hxNH⟩ : ↥(N ⊓ H)) = q := by
        rw [orderOf_mk, hx2_order]
      exact hord ▸ orderOf_dvd_natCard (⟨(x : A) ^ 2 ^ k, hxNH⟩ : ↥(N ⊓ H))
    exact (hN q hq hq_dvd).resolve_left hq2

private theorem s16t3_inf_cTilde_sup (hset : Setting16 D V₀ V L)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    {YL YK : Subgroup G} (hYL : S16t3CoverL D V₀ V hV (lBar V₀ V hV L) YL)
    (hYK : S16t3CoverK D V₀ V hV (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) YK) :
    (YL ⊔ YK) ⊓ F11.CTilde D.M V₀ V =
      (YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V) := by
  have hYLle : YL ≤ D.M := hYL.1
  have hYKle : YK ≤ D.M := hYK.1
  have hYLbar : barSub V₀ V hV YL = lBar V₀ V hV L := hYL.2.2.1
  have hYKbar : barSub V₀ V hV YK =
      s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := hYK.2.2.1
  obtain ⟨N, _, hLleN, _, _, hNKbot, _, _⟩ := hT.structure_of_seven h7
  have hLbKb : lBar V₀ V hV L ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) = ⊥ := by
    have hle : lBar V₀ V hV L ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) ≤
        N ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) :=
      inf_le_inf_right _ hLleN
    rw [hNKbot] at hle
    exact le_bot_iff.1 hle
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hset.hyp16.hyp125.pairFacts.le_normalizer
      hset.hyp16.hyp125.pairFacts.le_normalizer₀
  have hMnorm : D.M ≤ normalizer (V : Set G) := hset.hyp16.hyp125.pairFacts.le_normalizer
  apply le_antisymm
  · intro z hz
    rcases hz with ⟨hzS, hzC⟩
    obtain ⟨y, hy, k, hk, hxeq⟩ := s16t3_exists_mul_of_mem_sup hYL.2.1 hYLle hYKle hzS
    have hzC' : y * k ∈ F11.CTilde D.M V₀ V := by
      rw [hxeq]; exact hzC
    have hyM : y ∈ D.M := hYLle hy
    have hkM : k ∈ D.M := hYKle hk
    have hystab : y ∈ stabTil V₀ V := hMstab hyM
    have hkstab : k ∈ stabTil V₀ V := hMstab hkM
    have hbar_y : actTil V₀ V hV ⟨y, hystab⟩ ∈ lBar V₀ V hV L := by
      have hmem : actTil V₀ V hV ⟨y, hystab⟩ ∈ barSub V₀ V hV YL :=
        actTil_mem_barSub V₀ V hV hy hystab
      rwa [hYLbar] at hmem
    have hbar_k : actTil V₀ V hV ⟨k, hkstab⟩ ∈
        s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := by
      have hmem : actTil V₀ V hV ⟨k, hkstab⟩ ∈ barSub V₀ V hV YK :=
        actTil_mem_barSub V₀ V hV hk hkstab
      rwa [hYKbar] at hmem
    have hzbar : actTil V₀ V hV ⟨y * k, mul_mem hystab hkstab⟩ = 1 := by
      obtain ⟨hh, hh'⟩ := ((mem_cTilde_iff hV hMnorm).1 hzC').2
      convert hh' using 2
    have hprod : actTil V₀ V hV ⟨y, hystab⟩ * actTil V₀ V hV ⟨k, hkstab⟩ = 1 := by
      rw [← map_mul]
      rw [show (⟨y, hystab⟩ * ⟨k, hkstab⟩ : stabTil V₀ V) =
        ⟨y * k, mul_mem hystab hkstab⟩ from Subtype.ext rfl]
      exact hzbar
    have hbar_k_bot : actTil V₀ V hV ⟨k, hkstab⟩ = 1 := by
      have hk_inv : actTil V₀ V hV ⟨k, hkstab⟩ = (actTil V₀ V hV ⟨y, hystab⟩)⁻¹ :=
        eq_inv_of_mul_eq_one_right hprod
      have hk_L : actTil V₀ V hV ⟨k, hkstab⟩ ∈ lBar V₀ V hV L :=
        hk_inv.symm ▸ inv_mem hbar_y
      have hbot : actTil V₀ V hV ⟨k, hkstab⟩ ∈
          lBar V₀ V hV L ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) :=
        ⟨hk_L, hbar_k⟩
      rw [hLbKb] at hbot
      exact Subgroup.mem_bot.1 hbot
    have hbar_y_bot : actTil V₀ V hV ⟨y, hystab⟩ = 1 := by
      rw [hbar_k_bot, mul_one] at hprod
      exact hprod
    have hyC : y ∈ YL ⊓ F11.CTilde D.M V₀ V :=
      ⟨hy, (mem_cTilde_iff hV hMnorm).2 ⟨hyM, hystab, hbar_y_bot⟩⟩
    have hkC : k ∈ YK ⊓ F11.CTilde D.M V₀ V :=
      ⟨hk, (mem_cTilde_iff hV hMnorm).2 ⟨hkM, hkstab, hbar_k_bot⟩⟩
    have hmul : y * k ∈ (YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V) := by
      refine mul_mem ?_ ?_
      · exact (le_sup_left : (YL ⊓ F11.CTilde D.M V₀ V) ≤
            (YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V)) hyC
      · exact (le_sup_right : (YK ⊓ F11.CTilde D.M V₀ V) ≤
            (YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V)) hkC
    rwa [hxeq] at hmul
  · exact sup_le
      (le_inf (le_trans inf_le_left le_sup_left) inf_le_right)
      (le_inf (le_trans inf_le_left le_sup_right) inf_le_right)

private theorem s16t3_inf_Y_eq_pgroup (hset : Setting16 D V₀ V L)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    {YL YK : Subgroup G} (hYL : S16t3CoverL D V₀ V hV (lBar V₀ V hV L) YL)
    (hYK : S16t3CoverK D V₀ V hV (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) YK) :
    IsPGroup 2 ↥(YL ⊓ YK) := by
  have hYLle : YL ≤ D.M := hYL.1
  have hYKle : YK ≤ D.M := hYK.1
  have hYLbar : barSub V₀ V hV YL = lBar V₀ V hV L := hYL.2.2.1
  have hYKbar : barSub V₀ V hV YK =
      s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := hYK.2.2.1
  have hYKC : IsPGroup 2 ↥(YK ⊓ F11.CTilde D.M V₀ V) := hYK.2.2.2
  obtain ⟨N, _, hLleN, _, _, hNKbot, _, _⟩ := hT.structure_of_seven h7
  have hLbKb : lBar V₀ V hV L ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) = ⊥ := by
    have hle : lBar V₀ V hV L ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) ≤
        N ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) :=
      inf_le_inf_right _ hLleN
    rw [hNKbot] at hle
    exact le_bot_iff.1 hle
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hset.hyp16.hyp125.pairFacts.le_normalizer
      hset.hyp16.hyp125.pairFacts.le_normalizer₀
  have hMnorm : D.M ≤ normalizer (V : Set G) := hset.hyp16.hyp125.pairFacts.le_normalizer
  have hbarR_bot : barSub V₀ V hV (YL ⊓ YK) = ⊥ := by
    apply le_bot_iff.1
    calc barSub V₀ V hV (YL ⊓ YK) ≤ barSub V₀ V hV YL ⊓ barSub V₀ V hV YK :=
          le_inf (barSub_mono V₀ V hV inf_le_left) (barSub_mono V₀ V hV inf_le_right)
      _ = lBar V₀ V hV L ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := by
          rw [hYLbar, hYKbar]
      _ = ⊥ := hLbKb
  have hRleC : YL ⊓ YK ≤ F11.CTilde D.M V₀ V := by
    rw [cTilde_eq_preBarSub_bot hV hMnorm, ← hbarR_bot]
    exact le_preBarSub_barSub hV (le_trans inf_le_left hYLle)
      (le_trans inf_le_left (hYLle.trans hMstab))
  exact hYKC.to_le (le_inf inf_le_right hRleC)

theorem s16t3_barSub_sup {X Y : Subgroup G} (hX : X ≤ stabTil V₀ V)
    (hY : Y ≤ stabTil V₀ V) :
    barSub V₀ V hV (X ⊔ Y) = barSub V₀ V hV X ⊔ barSub V₀ V hV Y := by
  unfold barSub
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem s16t3_prime_dvd_card_of_sup_of_normal_amb {N P H : Subgroup G}
    (hN : (N.subgroupOf (N ⊔ P)).Normal) (hNH : H ≤ N ⊔ P)
    (hNp : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥(N ⊓ H) → q = 2 ∨ q = 3)
    (hP : IsPGroup 2 ↥P) {q : ℕ} (hq : q.Prime) (hqH : q ∣ Nat.card ↥H) : q = 2 ∨ q = 3 := by
  haveI := hN
  have hsup : N.subgroupOf (N ⊔ P) ⊔ P.subgroupOf (N ⊔ P) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hNp' : ∀ r : ℕ, r.Prime →
      r ∣ Nat.card ↥((N.subgroupOf (N ⊔ P)) ⊓ (H.subgroupOf (N ⊔ P))) → r = 2 ∨ r = 3 := by
    intro r hr hrdvd
    refine hNp r hr ?_
    have h : (N.subgroupOf (N ⊔ P)) ⊓ (H.subgroupOf (N ⊔ P)) =
        (N ⊓ H).subgroupOf (N ⊔ P) :=
      (Subgroup.comap_inf N H (N ⊔ P).subtype).symm
    rwa [h, s16t3_card_subgroupOf (le_trans inf_le_left le_sup_left)] at hrdvd
  have hqH' : q ∣ Nat.card ↥(H.subgroupOf (N ⊔ P)) := by
    rwa [s16t3_card_subgroupOf hNH]
  exact s16t3_prime_dvd_card_of_sup_of_normal hsup hNp' hP.comap_subtype hq hqH'

public theorem s16t3_barSub_sup_eq_Mbar (hset : Setting16 D V₀ V L)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    {YL YK : Subgroup G} (hYL : S16t3CoverL D V₀ V hV (lBar V₀ V hV L) YL)
    (hYK : S16t3CoverK D V₀ V hV (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) YK) :
    barSub V₀ V hV (YL ⊔ YK ⊔ D.T) = Mbar D.M V₀ V hV := by
  have hMstab : D.M ≤ stabTil V₀ V :=
    le_stabTil hset.hyp16.hyp125.pairFacts.le_normalizer
      hset.hyp16.hyp125.pairFacts.le_normalizer₀
  have hTsyl : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
  have hTbar : IsSylowIn 2 (barSub V₀ V hV D.T) (Mbar D.M V₀ V hV) :=
    s16c1_barSub_sylow hMstab hTsyl
  obtain ⟨N, hNleM, hLleN, -, hcomm, hNKbot, hNKsup, -⟩ := hT.structure_of_seven h7
  have hNnorm : (N.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNleM]
    have hKcent : s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) ≤
        Subgroup.centralizer (N : Set (MulAut (Vtil V₀ V hV))) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      exact hcomm n hn k hk
    calc Mbar D.M V₀ V hV
        = N ⊔ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := hNKsup.symm
      _ ≤ Subgroup.normalizer (N : Set (MulAut (Vtil V₀ V hV))) :=
          sup_le Subgroup.le_normalizer
            (hKcent.trans (Subgroup.centralizer_le_normalizer _))
  have hLbarM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := le_trans hLleN hNleM
  have hKbarM : s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) ≤ Mbar D.M V₀ V hV :=
    inf_le_left
  have hLbarNorm : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLbarM).mpr hT.normal
  have hmod : (lBar V₀ V hV L ⊔ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) ⊓ N =
      lBar V₀ V hV L := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨hxLK, hxN⟩
      have hxM : x ∈ Mbar D.M V₀ V hV := (sup_le hLbarM hKbarM) hxLK
      haveI := hLbarNorm
      have hx' : (⟨x, hxM⟩ : ↥(Mbar D.M V₀ V hV)) ∈
          ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)) ⊔
            ((s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)).subgroupOf
              (Mbar D.M V₀ V hV)) := by
        rw [← Subgroup.subgroupOf_sup hLbarM hKbarM]
        exact hxLK
      obtain ⟨l, hl, k, hk, hlk⟩ :=
        (Subgroup.mem_sup_of_normal_left
          (s := (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV))
          (t := (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)).subgroupOf
            (Mbar D.M V₀ V hV))).1 hx'
      have hval : (l : MulAut (Vtil V₀ V hV)) * (k : MulAut (Vtil V₀ V hV)) = x :=
        congrArg Subtype.val hlk
      have hkN : (k : MulAut (Vtil V₀ V hV)) ∈ N := by
        have hk_eq : (k : MulAut (Vtil V₀ V hV)) =
            (l : MulAut (Vtil V₀ V hV))⁻¹ * x := by
          rw [← hval]; group
        rw [hk_eq]
        exact N.mul_mem (N.inv_mem (hLleN hl)) hxN
      have hkbot : (k : MulAut (Vtil V₀ V hV)) ∈ (⊥ : Subgroup (MulAut (Vtil V₀ V hV))) := by
        rw [← hNKbot]
        exact ⟨hkN, hk⟩
      have hk1 : (k : MulAut (Vtil V₀ V hV)) = 1 := Subgroup.mem_bot.1 hkbot
      have hxeq : (⟨x, hxM⟩ : ↥(Mbar D.M V₀ V hV)) = l := by
        have hk1' : k = 1 := Subtype.ext hk1
        rw [hlk.symm, hk1', mul_one]
      have hxval : x = (l : MulAut (Vtil V₀ V hV)) := congrArg Subtype.val hxeq
      rw [hxval]
      exact hl
    · exact le_inf le_sup_left hLleN
  have hthirds : ∀ a b c : MulAut (Vtil V₀ V hV), a ∈ N → b ∈ N → c ∈ N →
      a⁻¹ * b ∈ lBar V₀ V hV L ∨ a⁻¹ * c ∈ lBar V₀ V hV L ∨
        b⁻¹ * c ∈ lBar V₀ V hV L := by
    intro a b c ha hb hc
    have h1 := hT.index_kBar_le_two h7 (hNleM ha) (hNleM hb) (hNleM hc)
    have habN : a⁻¹ * b ∈ N := N.mul_mem (N.inv_mem ha) hb
    have hacN : a⁻¹ * c ∈ N := N.mul_mem (N.inv_mem ha) hc
    have hbcN : b⁻¹ * c ∈ N := N.mul_mem (N.inv_mem hb) hc
    rcases h1 with h1 | h1 | h1
    · left
      have hmem : a⁻¹ * b ∈ (lBar V₀ V hV L ⊔
          s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) ⊓ N := ⟨h1, habN⟩
      rwa [hmod] at hmem
    · right; left
      have hmem : a⁻¹ * c ∈ (lBar V₀ V hV L ⊔
          s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) ⊓ N := ⟨h1, hacN⟩
      rwa [hmod] at hmem
    · right; right
      have hmem : b⁻¹ * c ∈ (lBar V₀ V hV L ⊔
          s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) ⊓ N := ⟨h1, hbcN⟩
      rwa [hmod] at hmem
  have hNle : N ≤ lBar V₀ V hV L ⊔ barSub V₀ V hV D.T :=
    s16t3_le_sup_of_sylow hNleM hNnorm hLleN hthirds hTbar
  apply le_antisymm
  · exact barSub_mono V₀ V hV (sup_le (sup_le hYL.1 hYK.1) D.sylowM.le)
  · have hYLstab : YL ≤ stabTil V₀ V := hYL.1.trans hMstab
    have hYKstab : YK ≤ stabTil V₀ V := hYK.1.trans hMstab
    have hTstab : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMstab
    have hbar2 : barSub V₀ V hV (YL ⊔ YK ⊔ D.T) =
        barSub V₀ V hV (YL ⊔ YK) ⊔ barSub V₀ V hV D.T :=
      s16t3_barSub_sup (sup_le hYLstab hYKstab) hTstab
    have hbar1 : barSub V₀ V hV (YL ⊔ YK) =
        barSub V₀ V hV YL ⊔ barSub V₀ V hV YK :=
      s16t3_barSub_sup hYLstab hYKstab
    rw [hbar2, hbar1, hYL.2.2.1, hYK.2.2.1]
    exact s16t3_le_sup_of_sup_eq hNKsup hNle

public theorem s16t3_prime_dvd_card_inf_cTilde (hset : Setting16 D V₀ V L)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    {YL YK : Subgroup G} (hYL : S16t3CoverL D V₀ V hV (lBar V₀ V hV L) YL)
    (hYK : S16t3CoverK D V₀ V hV (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) YK) :
    ∀ p : ℕ, p.Prime →
      p ∣ Nat.card ↥((YL ⊔ YK ⊔ D.T) ⊓ F11.CTilde D.M V₀ V) → p = 2 ∨ p = 3 := by
  have hMnorm : D.M ≤ normalizer (V : Set G) :=
    hset.hyp16.hyp125.pairFacts.le_normalizer
  have hMnorm₀ : D.M ≤ normalizer (V₀ : Set G) :=
    hset.hyp16.hyp125.pairFacts.le_normalizer₀
  have hCnorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := by
    refine ⟨fun c hc m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    simpa using uc22p22q_ctilde_conj_mem hMnorm hMnorm₀ m.2 hc
  haveI hYLn : (YL.subgroupOf D.M).Normal := hYL.2.1
  haveI hCn : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := hCnorm
  haveI hYKn : (YK.subgroupOf D.M).Normal := hYK.2.1
  have hXleM : YL ⊓ F11.CTilde D.M V₀ V ≤ D.M := inf_le_left.trans hYL.1
  have hYleM : YK ⊓ F11.CTilde D.M V₀ V ≤ D.M := inf_le_left.trans hYK.1
  have hXMnorm : ((YL ⊓ F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := by
    have h : (YL ⊓ F11.CTilde D.M V₀ V).subgroupOf D.M =
        YL.subgroupOf D.M ⊓ (F11.CTilde D.M V₀ V).subgroupOf D.M :=
      Subgroup.comap_inf YL (F11.CTilde D.M V₀ V) D.M.subtype
    rw [h]; infer_instance
  have hXM : D.M ≤ Subgroup.normalizer ((YL ⊓ F11.CTilde D.M V₀ V : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXleM).1 hXMnorm
  have hXle : YL ⊓ F11.CTilde D.M V₀ V ≤
      (YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V) := le_sup_left
  have hXnorm' : ((YL ⊓ F11.CTilde D.M V₀ V).subgroupOf
      ((YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXle).mpr
      (le_trans (sup_le hXleM hYleM) hXM)
  have hjoin : ∀ q : ℕ, q.Prime →
      q ∣ Nat.card ↥((YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V)) →
      q = 2 ∨ q = 3 := by
    haveI := hXnorm'
    have hsup : ((YL ⊓ F11.CTilde D.M V₀ V).subgroupOf
          ((YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V))) ⊔
        ((YK ⊓ F11.CTilde D.M V₀ V).subgroupOf
          ((YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V))) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hXle le_sup_right, Subgroup.subgroupOf_self]
    intro q hq hqdiv
    refine s16t3_prime_dvd_card_of_sup_of_normal (A :=
        ↥((YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V)))
      (N := (YL ⊓ F11.CTilde D.M V₀ V).subgroupOf
        ((YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V)))
      (P := (YK ⊓ F11.CTilde D.M V₀ V).subgroupOf
        ((YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V)))
      (H := ⊤) hsup ?_ ?_ hq ?_
    · intro r hr hrdvd
      rw [inf_top_eq, s16t3_card_subgroupOf hXle] at hrdvd
      exact hYL.2.2.2.2.2.2.1 r hr hrdvd
    · exact hYK.2.2.2.comap_subtype
    · simpa using hqdiv
  have hSleM : YL ⊔ YK ⊔ D.T ≤ D.M := sup_le (sup_le hYL.1 hYK.1) D.sylowM.le
  have hYLYKnorm : ((YL ⊔ YK).subgroupOf D.M).Normal := by
    rw [Subgroup.subgroupOf_sup hYL.1 hYK.1]; infer_instance
  have hDMnorm : D.M ≤ Subgroup.normalizer ((YL ⊔ YK : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hYL.1 hYK.1)).1 hYLYKnorm
  have hNnorm : ((YL ⊔ YK).subgroupOf ((YL ⊔ YK) ⊔ D.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer (D.sylowM.le.trans hDMnorm))
  intro p hp hpdiv
  refine s16t3_prime_dvd_card_of_sup_of_normal_amb (N := YL ⊔ YK) (P := D.T)
    (H := (YL ⊔ YK ⊔ D.T) ⊓ F11.CTilde D.M V₀ V) hNnorm inf_le_left ?_
    D.sylowM.isPGroup hp hpdiv
  intro q hq hqdvd
  have h1 : (YL ⊔ YK) ⊓ ((YL ⊔ YK ⊔ D.T) ⊓ F11.CTilde D.M V₀ V) =
      (YL ⊓ F11.CTilde D.M V₀ V) ⊔ (YK ⊓ F11.CTilde D.M V₀ V) :=
    s16t3_inf_inf_eq_of_inf_eq le_sup_left (s16t3_inf_cTilde_sup hset hT h7 hYL hYK)
  rw [h1] at hqdvd
  exact hjoin q hq hqdvd

theorem s16t3_join_inf_cTilde (hset : Setting16 D V₀ V L)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    {YL YK : Subgroup G} (hYL : S16t3CoverL D V₀ V hV (lBar V₀ V hV L) YL)
    (hYK : S16t3CoverK D V₀ V hV (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) YK) :
    YL ⊔ YK ⊔ D.T ≤ D.M ∧ barSub V₀ V hV (YL ⊔ YK ⊔ D.T) = Mbar D.M V₀ V hV ∧
      IsPGroup 2 ↥(YL ⊓ YK) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card ↥((YL ⊔ YK ⊔ D.T) ⊓ F11.CTilde D.M V₀ V) →
        p = 2 ∨ p = 3) := by
  refine ⟨?_, s16t3_barSub_sup_eq_Mbar hset hT h7 hYL hYK,
    s16t3_inf_Y_eq_pgroup hset hT h7 hYL hYK,
    s16t3_prime_dvd_card_inf_cTilde hset hT h7 hYL hYK⟩
  exact sup_le (sup_le hYL.1 hYK.1) D.sylowM.le

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
