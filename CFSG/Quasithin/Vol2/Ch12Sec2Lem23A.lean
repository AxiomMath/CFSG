module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem23QX
public import CFSG.Quasithin.Background.B4L3Syl

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

namespace Lem22

theorem L3_center_cent : ∀ s : L3.Γ, L3.IsInvol s → ∀ x ∈ L3.cent s,
    (∀ y ∈ L3.cent s, x * y = y * x) → x = 1 ∨ x = s := by
  unfold L3.IsInvol L3.cent
  decide +kernel

theorem L3_eq_one_of_normalizes {S : Subgroup L3.Γ} (hS : Nat.card S = 8) {γ : L3.Γ}
    (hγ3 : γ ^ 3 = 1) (hγS : γ ∈ Subgroup.normalizer (S : Set L3.Γ)) : γ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 3) (by rw [hS]; norm_num)
  have : Nontrivial S := by
    rw [← Finite.one_lt_card_iff_nontrivial, hS]
    norm_num
  have hZnt := hS2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center ↥S) := hS2.to_subgroup _
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp hZ2
  have hZgt : 1 < Nat.card (Subgroup.center ↥S) := Finite.one_lt_card_iff_nontrivial.mpr hZnt
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    omega
  have hdvd : 2 ∣ Nat.card (Subgroup.center ↥S) := by
    rw [hj]
    exact dvd_pow_self 2 hj0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥S)) 2 hdvd
  set s : L3.Γ := ((z : ↥S) : L3.Γ) with hsdef
  have hs2 : s * s = 1 := by
    have h1 : z ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz] at this
    have := congrArg (fun x : ↥(Subgroup.center ↥S) => ((x : ↥S) : L3.Γ)) h1
    simpa [pow_two] using this
  have hs1 : s ≠ 1 := by
    intro h0
    have : z = 1 := Subtype.ext (Subtype.ext h0)
    rw [this, orderOf_one] at hz
    omega
  have hsInv : L3.IsInvol s := ⟨hs2, hs1⟩
  have hsS : s ∈ S := (z : ↥S).2
  have hsc : ∀ y ∈ S, y * s = s * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
  have hSC : S = Subgroup.centralizer ({s} : Set L3.Γ) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro y hy
      rw [Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (hsc y hy).symm
    · rw [card_centralizer_L3 hsInv, hS]
  set x := γ * s * γ⁻¹ with hx
  have hxc : ∀ y ∈ S, x * y = y * x := by
    intro y hy
    have hy' : γ⁻¹ * y * γ ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hγS) y).mp hy
      simpa using this
    have h1 := hsc _ hy'
    calc x * y = γ * (s * (γ⁻¹ * y * γ)) * γ⁻¹ := by rw [hx]; group
      _ = γ * ((γ⁻¹ * y * γ) * s) * γ⁻¹ := by rw [h1]
      _ = y * x := by rw [hx]; group
  have hmemC : ∀ y : L3.Γ, y ∈ L3.cent s ↔ y ∈ S := by
    intro y
    rw [hSC, Subgroup.mem_centralizer_iff]
    simp only [L3.cent, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_singleton_iff,
      forall_eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have hx1 : x ≠ 1 := by
    intro h0
    apply hs1
    have : s = γ⁻¹ * x * γ := by rw [hx]; group
    rw [this, h0]
    group
  have hxs : x = s := by
    refine (L3_center_cent s hsInv x ((hmemC x).mpr ?_) fun y hy => hxc y ((hmemC y).mp hy)
      ).resolve_left hx1
    exact (Subgroup.mem_normalizer_iff.mp hγS s).mp hsS
  have hγs : γ ∈ S := by
    rw [hSC, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    calc s * γ = x * γ := by rw [hxs]
      _ = γ * s := by rw [hx]; group
  have h8 : γ ^ 8 = 1 := by
    have h1 : orderOf (⟨γ, hγs⟩ : S) ∣ Nat.card S := orderOf_dvd_natCard _
    rw [hS] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
    simpa using congrArg Subtype.val h2
  calc γ = (γ ^ 3) ^ 3 * (γ ^ 8)⁻¹ := by group
    _ = 1 := by rw [hγ3, h8]; group

variable {G : Type} [Group G] [Finite G]

theorem exists_eq_inv_mul_conj {A : Subgroup G} {z : G} (hzA : ∀ a ∈ A, z * a * z⁻¹ ∈ A)
    (hfix : ∀ a ∈ A, z * a * z⁻¹ = a → a = 1) :
    ∀ a ∈ A, ∃ b ∈ A, a = b⁻¹ * (z * b * z⁻¹) := by
  let θ : ↥A → ↥A := fun b =>
    ⟨(b : G)⁻¹ * (z * (b : G) * z⁻¹), A.mul_mem (A.inv_mem b.2) (hzA b b.2)⟩
  have hθ : Function.Injective θ := by
    intro b₁ b₂ h12
    have h := congrArg Subtype.val h12
    simp only [θ] at h
    have hb : (b₂ : G) * (b₁ : G)⁻¹ ∈ A := A.mul_mem b₂.2 (A.inv_mem b₁.2)
    have hz1 : z * (b₁ : G) * z⁻¹ ∈ A := hzA _ b₁.2
    have hz2 : z * (b₂ : G) * z⁻¹ ∈ A := hzA _ b₂.2
    have hfx : z * ((b₂ : G) * (b₁ : G)⁻¹) * z⁻¹ = (b₂ : G) * (b₁ : G)⁻¹ := by
      have e1 : z * ((b₂ : G) * (b₁ : G)⁻¹) * z⁻¹ =
          (z * (b₂ : G) * z⁻¹) * (z * (b₁ : G) * z⁻¹)⁻¹ := by group
      rw [e1]
      have e2 : z * (b₂ : G) * z⁻¹ = (b₂ : G) * ((b₁ : G)⁻¹ * (z * (b₁ : G) * z⁻¹)) := by
        rw [h]
        group
      rw [e2]
      group
    have h1 := hfix _ hb hfx
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  intro a ha
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.mp hθ) ⟨a, ha⟩
  exact ⟨b, b.2, (congrArg Subtype.val hb).symm⟩

namespace Extra3

variable {T L V H P U I : Subgroup G} {h : G}

theorem mem_of_eq_mul (h331 : Stmt3_3_1) (e : Extra3 T L V H P U I h) {x l t : G} (hl : l ∈ L)
    (ht : t ∈ T) (hx : x = l * t) (hx3 : x ^ 3 = 1) : x ∈ L := by
  obtain ⟨hHs, -⟩ := e.pre
  have hT2 : IsPGroup 2 ↥T := (Lem7.minParabolic h331 e.hyp hHs).isSylow.2.1
  have hTL : ∀ y ∈ L, t * y * t⁻¹ ∈ L := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (e.hyp.normalizes ht) y).mp hy
  have ht3 : t ^ 3 ∈ L := by
    have e1 : (l * (t * l * t⁻¹) * (t * (t * l * t⁻¹) * t⁻¹)) * (t * t * t) = x * x * x := by
      rw [hx]
      group
    have hx3' : x * x * x = 1 := by rw [← pow_three']; exact hx3
    rw [hx3'] at e1
    rw [pow_three', eq_inv_of_mul_eq_one_right e1]
    exact L.inv_mem (L.mul_mem (L.mul_mem hl (hTL l hl)) (hTL _ (hTL l hl)))
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (orderOf t) 3 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one htk)
      (Nat.Coprime.pow_left _ (by norm_num))
  have htL : t ∈ L := B6.mem_of_pow_mem_of_coprime ht3 hcop
  rw [hx]
  exact L.mul_mem hl htL

theorem le_normalizer_frattini_sup_pCore (h331 : Stmt3_3_1) (e : Extra3 T L V H P U I h) :
    T ≤ Subgroup.normalizer
      (((frattini ↥P).map P.subtype ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
  obtain ⟨hHs, hsol, hp, hp2, hPp, hPH, hPi, -, -, hhP, hhM, -⟩ := e.pre
  have hh1 : h ≠ 1 := fun h1 => hhM (h1 ▸ Subgroup.one_mem _)
  have hP1 : P ≠ ⊥ := fun h0 => hh1 (by rw [h0] at hhP; exact Subgroup.mem_bot.mp hhP)
  have hTH : T ≤ H := (Lem7.minParabolic h331 e.hyp hHs).isSylow.1
  exact fun t ht => le_normalizer_frattini_sup hPH
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    (fun g hg => exists_mul_mem_normalizer h331 e.hyp hHs hsol hp hp2 hPp hPH hPi hP1 hg)
    (hTH ht)

theorem frattini_le (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    (frattini ↥P).map P.subtype ≤ L := by
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  obtain ⟨hHs, -, -, -, -, hPH, -, -, hPΦ, -⟩ := e.pre
  have hmin := Lem7.minParabolic h331 e.hyp hHs
  have hT2 : IsPGroup 2 ↥T := hmin.isSylow.2.1
  have hQHT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hmin.isSylow
  have hΦM : Φ ≤ Subgroup.normalizer (L : Set G) := by
    rw [hΦdef, ← hPΦ]
    exact inf_le_right
  have hΦQ : Φ ≤ Subgroup.normalizer (Q : Set G) := e.frattini_le_normalizer_CT h331 h1222
  have hTN : T ≤ Subgroup.normalizer ((Φ ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    e.le_normalizer_frattini_sup_pCore h331
  have hΦN : Φ ≤ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    (frattini_map_le P).trans (hPH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := fun c hc => e.hyp.normalizes hc.1
  have hTLQ : T ≤ L ⊔ Q := e.concl.2.2.2.2
  intro f hf
  by_contra hfL
  have hf1 : f ≠ 1 := fun h0 => hfL (h0 ▸ L.one_mem)
  have hΦL : ∀ g ∈ Φ, g ∈ L → g = 1 := by
    intro g hg hgL
    by_contra hg1
    apply hfL
    have hf' := hf
    have hzp : Subgroup.zpowers g = Φ := e.zpowers_eq hg hg1
    rw [← hzp] at hf'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf'
    exact L.zpow_mem hgL k
  have hfT : ∀ t ∈ T, f * t * f⁻¹ ∈ T := by
    intro t ht
    have h1 : t * f⁻¹ * t⁻¹ ∈ Φ ⊔ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp (hTN ht) f⁻¹).mp (Subgroup.mem_sup_left (Φ.inv_mem hf))
    have h2 : f * (t * f⁻¹ * t⁻¹) ∈ Φ ⊔ pCoreOf 2 H :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hf) h1
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hΦN] at h2
    obtain ⟨f', hf', q, hq, hfq⟩ := h2
    have ht' : t ∈ L ⊔ Q := hTLQ ht
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hQN] at ht'
    obtain ⟨l, hl, c, hc, hlc⟩ := ht'
    have hfl : f * l * f⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hΦM hf) l).mp hl
    have hfc : f * c * f⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hΦQ hf) c).mp hc
    have hqtT : q * t ∈ T := T.mul_mem (hQHT hq) ht
    have hft : f * t * f⁻¹ = f' * (q * t) := by
      calc f * t * f⁻¹ = (f * (t * f⁻¹ * t⁻¹)) * t := by group
        _ = f' * q * t := by rw [← hfq]
        _ = f' * (q * t) := by group
    have he : f' = (f * l * f⁻¹) * ((f * c * f⁻¹) * (q * t)⁻¹) := by
      have hft' : f * t * f⁻¹ = (f * l * f⁻¹) * (f * c * f⁻¹) := by
        rw [← hlc]
        group
      calc f' = (f * t * f⁻¹) * (q * t)⁻¹ := by rw [hft]; group
        _ = (f * l * f⁻¹) * ((f * c * f⁻¹) * (q * t)⁻¹) := by rw [hft']; group
    have hf'L : f' ∈ L := e.mem_of_eq_mul h331 hfl (T.mul_mem hfc.1 (T.inv_mem hqtT)) he
      (e.exp f' (frattini_map_le P hf'))
    rw [hft, hΦL f' hf' hf'L, one_mul]
    exact hqtT
  obtain ⟨-, -, htop, ⟨hcommV, hnatV⟩, -⟩ := e.concl
  obtain ⟨DV⟩ := hnatV.toL3Coord
  obtain ⟨-, -, hall⟩ := ((h1222 G T e.hyp.simple e.hyp.nonabelian e.hyp.qtke
    e.hyp.sylow).resolve_left e.hyp.notAlt) L e.hyp.maximal e.hyp.faithful e.hyp.quasisimple
  obtain ⟨⟨-, hTV, -, -⟩, -, -, -, -⟩ := hall V e.hyp.irrPlus
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := e.hyp.irrPlus.2.2.1
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  have hTLT : IsSylowTwoOf T (L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo e.hyp.sylow le_sup_right
  set φ := A4.actionOn V (L ⊔ T) hLTV with hφ
  have hφs : Function.Surjective φ := by
    intro a
    have ha : a ∈ autOn L V := htop ▸ Subgroup.mem_top a
    obtain ⟨⟨l, hl⟩, rfl⟩ := (A4.mem_autOn_iff hLV).mp ha
    exact ⟨⟨l, Subgroup.mem_sup_left hl⟩, rfl⟩
  have hmap : (T.subgroupOf (L ⊔ T)).map φ = autOn T V := by
    ext a
    rw [Subgroup.mem_map, A4.mem_autOn_iff hTV]
    constructor
    · rintro ⟨⟨t, htLT⟩, ht, rfl⟩
      exact ⟨⟨t, Subgroup.mem_subgroupOf.mp ht⟩, rfl⟩
    · rintro ⟨⟨t, ht⟩, rfl⟩
      exact ⟨⟨t, Subgroup.mem_sup_right ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have hidx : ¬ 2 ∣ (autOn T V).index := by
    rw [← hmap]
    intro h2
    exact hTLT.2.2 (h2.trans (Subgroup.index_map_dvd _ hφs))
  have hTsub : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer (V : Set G))) := by
    intro x
    obtain ⟨k, hk⟩ := hT2 ⟨((x : ↥(Subgroup.normalizer (V : Set G))) : G),
      Subgroup.mem_subgroupOf.mp x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hsyl : IsSylowTwoOf (autOn T V) (autOn L V) := by
    refine ⟨htop ▸ le_top, hTsub.map (conjAct V), ?_⟩
    rw [htop]
    show ¬ 2 ∣ (autOn T V).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hidx
  have h8 : Nat.card (autOn T V) = 8 := DV.card_sylow hsyl
  have hfV : f ∈ Subgroup.normalizer (V : Set G) := e.ΦV hf
  set g₀ : MulAut ↥V := conjAct V ⟨f, hfV⟩ with hg₀
  obtain ⟨γ, hγ⟩ := DV.exists_rho (htop ▸ Subgroup.mem_top g₀ : g₀ ∈ autOn L V)
  set S : Subgroup L3.Γ := (autOn T V).comap DV.rho with hS
  have hrange : DV.rho.range = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨δ, hδ⟩ := DV.exists_rho (htop ▸ Subgroup.mem_top a : a ∈ autOn L V)
    exact ⟨δ, hδ⟩
  have hS8 : Nat.card S = 8 := by
    have h1 : S.map DV.rho = autOn T V := by
      rw [hS, Subgroup.map_comap_eq, hrange, top_inf_eq]
    rw [← Subgroup.card_map_of_injective DV.rho_injective, h1, h8]
  have hγ3 : γ ^ 3 = 1 := by
    apply DV.rho_injective
    rw [map_pow, hγ, map_one, hg₀, ← map_pow]
    have h3 : (⟨f, hfV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using e.exp f (frattini_map_le P hf))
    rw [h3, map_one]
  have hγS : γ ∈ Subgroup.normalizer (S : Set L3.Γ) := by
    refine Sec121Swap.mem_normalizer_of_conj_mem fun s hs => ?_
    show DV.rho (γ * s * γ⁻¹) ∈ autOn T V
    have hs' : DV.rho s ∈ autOn T V := hs
    obtain ⟨⟨t, ht⟩, hts⟩ := (A4.mem_autOn_iff hTV).mp hs'
    rw [map_mul, map_mul, map_inv, hγ, ← hts, A4.mem_autOn_iff hTV]
    refine ⟨⟨f * t * f⁻¹, hfT t ht⟩, ?_⟩
    rw [hg₀, ← map_inv]
    ext v
    show f * t * f⁻¹ * (v : G) * (f * t * f⁻¹)⁻¹ = f * (t * (f⁻¹ * (v : G) * f⁻¹⁻¹) * t⁻¹) * f⁻¹
    group
  have hγ1 := L3_eq_one_of_normalizes hS8 hγ3 hγS
  have hg1 : g₀ = 1 := by rw [← hγ, hγ1, map_one]
  have hfC : f ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff.mp hg1
  exact hf1 (e.eq_one_of_comm_inf hf fun u hu =>
    ((Subgroup.mem_centralizer_iff.mp hfC) u hu.1).symm)

theorem W_le (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (e : Extra3 T L V H P U I h) :
    conjClosure (V ⊓ pCoreOf 2 H) P ≤ L := by
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  set W := conjClosure (V ⊓ pCoreOf 2 H) P with hW
  obtain ⟨hHs, -, -, -, -, hPH, -⟩ := e.pre
  have hTH : T ≤ H := (Lem7.minParabolic h331 e.hyp hHs).isSylow.1
  have hQT : pCoreOf 2 H ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (Lem7.minParabolic h331 e.hyp hHs).isSylow
  have hΦL := e.frattini_le h331 h1222
  have hHW := e.le_normalizer_W h331 h1222
  have hWZ := e.W_le_center
  have hWC := e.W_inf_centralizer h331 h1222
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥Φ := isCyclic_of_prime_card e.cardΦ
  obtain ⟨⟨z, hzΦ⟩, hgen⟩ := hcyc.exists_generator
  have hzW : ∀ a ∈ W, z * a * z⁻¹ ∈ W := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hHW (hPH (frattini_map_le P hzΦ))) a).mp ha
  have hfix : ∀ a ∈ W, z * a * z⁻¹ = a → a = 1 := by
    intro a ha hza
    have hza' : z * a = a * z := by
      calc z * a = (z * a * z⁻¹) * z := by group
        _ = a * z := by rw [hza]
    have hac : a ∈ W ⊓ Subgroup.centralizer (Φ : Set G) := by
      refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨f, hf⟩)
      have hk' : z ^ k = f := by simpa using congrArg Subtype.val hk
      rw [← hk']
      exact Commute.zpow_left hza' k
    rw [hWC, Subgroup.mem_bot] at hac
    exact hac
  intro w hw
  obtain ⟨b, hb, rfl⟩ := exists_eq_inv_mul_conj hzW hfix w hw
  have hbT : b ∈ T := hQT (hWZ hb).1
  have hzL : z ∈ L := hΦL hzΦ
  have h1 : b⁻¹ * z * b ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (e.hyp.normalizes (T.inv_mem hbT)) z).mp hzL
    simpa using this
  have e1 : b⁻¹ * (z * b * z⁻¹) = (b⁻¹ * z * b) * z⁻¹ := by group
  rw [e1]
  exact L.mul_mem h1 (L.inv_mem hzL)

end Extra3

end Lem22

end CFSG.Quasithin.H13
