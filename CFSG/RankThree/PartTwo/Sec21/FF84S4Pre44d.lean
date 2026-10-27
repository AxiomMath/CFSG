module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre44c
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Inputs
public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre44dK

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

set_option maxRecDepth 200000 in
theorem cen_a8c : ∀ g : Perm (Fin 8),
    g * a8c = a8c * g → g * a8d = a8d * g →
    g * (swap 4 5 * swap 5 6) = (swap 4 5 * swap 5 6) * g →
    g * (swap 5 6 * swap 6 7) = (swap 5 6 * swap 6 7) * g →
    g = 1 ∨ g = a8c ∨ g = a8c⁻¹ := by
  intro g h1 h2 h3 h4
  have hc : ∀ x, g (a8c x) = a8c (g x) := fun x => Perm.ext_iff.1 h1 x
  have hd : ∀ x, g (a8d x) = a8d (g x) := fun x => Perm.ext_iff.1 h2 x
  have he : ∀ x, g ((swap 4 5 * swap 5 6 : Perm (Fin 8)) x) =
      (swap 4 5 * swap 5 6 : Perm (Fin 8)) (g x) := fun x => Perm.ext_iff.1 h3 x
  have hf : ∀ x, g ((swap 5 6 * swap 6 7 : Perm (Fin 8)) x) =
      (swap 5 6 * swap 6 7 : Perm (Fin 8)) (g x) := fun x => Perm.ext_iff.1 h4 x
  have e1 : g 1 = a8c (g 0) := (congrArg g (by decide : (1 : Fin 8) = a8c 0)).trans (hc 0)
  have e2 : g 2 = a8c (a8c (g 0)) := by
    rw [← e1, ← hc 1]
    exact congrArg g (by decide)
  have e4 : g 4 = a8d (g 3) := (congrArg g (by decide : (4 : Fin 8) = a8d 3)).trans (hd 3)
  have e5 : g 5 = a8d (a8d (g 3)) := by
    rw [← e4, ← hd 4]
    exact congrArg g (by decide)
  have e6 : g 6 = (swap 4 5 * swap 5 6 : Perm (Fin 8)) (a8d (a8d (g 3))) := by
    rw [← e5, ← he 5]
    exact congrArg g (by decide)
  have e7 : g 7 = (swap 5 6 * swap 6 7 : Perm (Fin 8))
      ((swap 4 5 * swap 5 6 : Perm (Fin 8)) (a8d (a8d (g 3)))) := by
    rw [← e6, ← hf 6]
    exact congrArg g (by decide)
  have hg : ∀ x, g x = S4K.cenA8cExt (g 0) (g 3) x := by
    intro x
    fin_cases x
    exacts [rfl, e1, e2, rfl, e4, e5, e6, e7]
  rcases S4K.cenA8cExt_check (g 0) (g 3)
      (fun x => by simp only [← hg]; exact hc x) (fun x => by simp only [← hg]; exact hd x)
      (fun x => by simp only [← hg]; exact he x) (fun x => by simp only [← hg]; exact hf x) with
    h | h | h
  · exact Or.inl (Perm.ext fun x => (hg x).trans (h x))
  · exact Or.inr (Or.inl (Perm.ext fun x => (hg x).trans (h x)))
  · exact Or.inr (Or.inr (Perm.ext fun x => (hg x).trans (h x)))

theorem sign_c456 : sign (swap (4 : Fin 8) 5 * swap 5 6) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  decide

theorem sign_c567 : sign (swap (5 : Fin 8) 6 * swap 6 7) = 1 := by
  rw [Perm.sign_mul, Perm.sign_swap (by decide), Perm.sign_swap (by decide)]
  decide

theorem K_simple60 (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    (hZ : Subgroup.center L = ⊥) : Nat.card K = 60 ∧ IsSimpleGroup K := by
  obtain ⟨θ, hker, -, hsurj, hb₁θ, -⟩ := theta_model hA h
  obtain ⟨-, hKmod, hKsup, hKb₁K, hKcen⟩ := h.hK
  have hKle : K ≤ L ⊓ Cen b₁ := hKsup ▸ le_sup_right
  have hKL : K ≤ L := hKle.trans inf_le_left
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  let f : ↥L →* Perm (Fin 8) :=
    θ.comp (Subgroup.inclusion (fun x hx => Subgroup.le_normalizer hx))
  have hfinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).2 fun x hx => ?_
    have hc : (x : G) ∈ CenS L := (hker ⟨x, Subgroup.le_normalizer x.2⟩).1 hx
    have hxc : x ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc g g.2)
    rw [hZ] at hxc
    exact Subgroup.mem_bot.1 hxc
  have hfb₁ : f ⟨b₁, hb₁L⟩ = a8c := hb₁θ
  have hlift : ∀ g₀ : Perm (Fin 8), sign g₀ = 1 → g₀ * a8c = a8c * g₀ →
      ∃ x : ↥L, f x = g₀ ∧ (x : G) ∈ Cen b₁ := by
    intro g₀ hg₀ hcomm
    obtain ⟨x, hx⟩ := hsurj g₀ (mem_alternatingGroup.2 hg₀)
    refine ⟨x, hx, ?_⟩
    have hc : f (x * ⟨b₁, hb₁L⟩ * x⁻¹ * ⟨b₁, hb₁L⟩⁻¹) = 1 := by
      have hx' : f x = g₀ := hx
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx', hfb₁]
      rw [hcomm]
      group
    have := hfinj (hc.trans (map_one f).symm)
    have e : (x : G) * b₁ * (x : G)⁻¹ * b₁⁻¹ = 1 := congrArg Subtype.val this
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc (x : G) * b₁ = ((x : G) * b₁ * (x : G)⁻¹ * b₁⁻¹) * (b₁ * x) := by group
      _ = b₁ * x := by rw [e, one_mul]
  have hZK : Subgroup.center ↥K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    set zG : G := (z : G) with hzG
    have hzL : zG ∈ L := hKL z.2
    have hsub : L ⊓ Cen b₁ ≤ Subgroup.centralizer ({zG} : Set G) := by
      rw [← hKsup]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_singleton_iff.1
          (hKcen z.2)).symm
      · intro k hk
        exact Subgroup.mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩))
    have hzcomm : ∀ x : ↥L, (x : G) ∈ Cen b₁ → x * ⟨zG, hzL⟩ = ⟨zG, hzL⟩ * x := by
      intro x hx
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1
        (hsub (Subgroup.mem_inf.2 ⟨x.2, hx⟩))
    have hfz : ∀ g₀ : Perm (Fin 8), (∃ x : ↥L, f x = g₀ ∧ (x : G) ∈ Cen b₁) →
        f ⟨zG, hzL⟩ * g₀ = g₀ * f ⟨zG, hzL⟩ := by
      rintro g₀ ⟨x, hx, hxc⟩
      rw [← hx, ← map_mul, ← map_mul, hzcomm x hxc |>.symm]
    have hb₁c : (⟨b₁, hb₁L⟩ : ↥L).1 ∈ Cen b₁ := Subgroup.mem_centralizer_singleton_iff.2 rfl
    have h1 := hfz a8c ⟨⟨b₁, hb₁L⟩, hfb₁, hb₁c⟩
    have h2 := hfz a8d (hlift a8d a8d_sign (by
      unfold a8c a8d
      decide +kernel))
    have h3 := hfz (swap 4 5 * swap 5 6) (hlift _ sign_c456 (by decide +kernel))
    have h4 := hfz (swap 5 6 * swap 6 7) (hlift _ sign_c567 (by decide +kernel))
    rcases cen_a8c (f ⟨zG, hzL⟩) h1.symm.symm h2.symm.symm h3.symm.symm h4.symm.symm with
      hz1 | hz1 | hz1
    · have e0 : zG = 1 := congrArg Subtype.val (hfinj (hz1.trans (map_one f).symm))
      exact Subtype.ext e0
    · exfalso
      have : (⟨zG, hzL⟩ : ↥L) = ⟨b₁, hb₁L⟩ := hfinj (hz1.trans hfb₁.symm)
      have hz : b₁ ∈ K := by
        have e0 : zG = b₁ := congrArg Subtype.val this
        rw [← e0]; exact z.2
      have hb : b₁ ∈ Subgroup.zpowers b₁ ⊓ K := Subgroup.mem_inf.2 ⟨Subgroup.mem_zpowers b₁, hz⟩
      rw [hKb₁K, Subgroup.mem_bot] at hb
      exact b₁_ne_one h hb
    · exfalso
      have : (⟨zG, hzL⟩ : ↥L) = ⟨b₁, hb₁L⟩⁻¹ := hfinj (by rw [hz1, map_inv, hfb₁])
      have hz : b₁⁻¹ ∈ K := by
        have e0 : zG = b₁⁻¹ := congrArg Subtype.val this
        rw [← e0]; exact z.2
      have hb : b₁⁻¹ ∈ Subgroup.zpowers b₁ ⊓ K :=
        Subgroup.mem_inf.2 ⟨inv_mem (Subgroup.mem_zpowers b₁), hz⟩
      rw [hKb₁K, Subgroup.mem_bot, inv_eq_one] at hb
      exact b₁_ne_one h hb
  obtain ⟨e5⟩ := CFSG.ComponentClassification.RankTwoClassical.nonempty_equiv_a5_of_psl hKmod
  have hinjq : Function.Injective (QuotientGroup.mk' (Subgroup.center ↥K)) := by
    refine (injective_iff_map_eq_one _).2 fun z hz => ?_
    have : z ∈ Subgroup.center ↥K := (QuotientGroup.eq_one_iff z).1 hz
    rw [hZK] at this
    exact Subgroup.mem_bot.1 this
  let eq0 : ↥K ≃* ↥K ⧸ Subgroup.center ↥K :=
    MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center ↥K))
      ⟨hinjq, QuotientGroup.mk'_surjective _⟩
  let eK : ↥K ≃* alternatingGroup (Fin 5) := eq0.trans e5
  refine ⟨by rw [Nat.card_congr eK.toEquiv, card_alt5], eK.isSimpleGroup⟩

theorem CY_b₂_trivial (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    (hX : Opp 3 (Cen b) = ⊥) (hodd : Odd (Nat.card (Opp 3 (Cen (b * b₁))))) :
    Opp 3 (Cen (b * b₁)) ⊓ Cen b₂ = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, ⟨n, hnN, hnb, hnb₁, hnb₂⟩⟩ := h.mono
  set Y := Opp 3 (Cen (b * b₁)) with hY
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  have hYc : Nat.Coprime (Nat.card Y) 6 := by
    have h2 : Nat.Coprime (Nat.card Y) 2 := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 fun hd => ?_)
      have := Nat.odd_iff.1 hodd
      omega
    have h3 : Nat.Coprime (Nat.card Y) 3 := (FF79.L14.Opp_coprime 3 (Cen (b * b₁))).symm
    simpa using Nat.Coprime.mul_right h2 h3
  have hYo : ∀ y ∈ Y, Nat.Coprime (orderOf y) 6 := fun y hy =>
    Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard Y hy) hYc
  have hYn : ∀ c ∈ Cen (b * b₁), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := fun c hc y hy =>
    FF79.L14.Opp_conj_mem hc hy
  have hn'b : n⁻¹ * b₁ * n = b := by rw [← hnb]; group
  have hn'b₁ : n⁻¹ * b₂ * n = b₁ := by rw [← hnb₁]; group
  have hn'b₂ : n⁻¹ * b * n = b₂ := by rw [← hnb₂]; group
  have hW : (Y ⊓ Cen b₂).map (MulAut.conj n).toMonoidHom ≤ Opp 3 (Cen b) := by
    refine le_X hA h ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have := conj_mem_cen (g := n) (Subgroup.mem_inf.1 hy).2
      rw [hnb₂] at this
      exact this
    · rintro _ ⟨y, hy, rfl⟩
      have := conj_mem_cen (g := n) (Opp_le 3 _ (Subgroup.mem_inf.1 hy).1)
      rwa [show n * (b * b₁) * n⁻¹ = b₁ * b₂ by
        calc n * (b * b₁) * n⁻¹ = (n * b * n⁻¹) * (n * b₁ * n⁻¹) := by group
          _ = b₁ * b₂ := by rw [hnb, hnb₁]] at this
    · rintro _ ⟨y, hy, rfl⟩
      show Nat.Coprime (orderOf (MulAut.conj n y)) 6
      rw [MulEquiv.orderOf_eq (MulAut.conj n) y]
      exact hYo y (Subgroup.mem_inf.1 hy).1
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (FF79.L14.Opp_coprime 3 (Cen (b * b₁)))
    · intro c hc w hw
      obtain ⟨hcb, hcL⟩ := Subgroup.mem_inf.1 hc
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hw
      have hcb₁ : c ∈ Cen b₁ := Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hcL b₁ hb₁L).symm
      have hcb₂ : c ∈ Cen b₂ := Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hcL b₂ hb₂L).symm
      have hcb₁b₂ : c ∈ Cen (b₁ * b₂) := by
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have e1 := Subgroup.mem_centralizer_singleton_iff.1 hcb₁
        have e2 := Subgroup.mem_centralizer_singleton_iff.1 hcb₂
        calc c * (b₁ * b₂) = (c * b₁) * b₂ := by rw [mul_assoc]
          _ = (b₁ * c) * b₂ := by rw [e1]
          _ = b₁ * (c * b₂) := by rw [mul_assoc]
          _ = b₁ * (b₂ * c) := by rw [e2]
          _ = (b₁ * b₂) * c := by rw [mul_assoc]
      have hc'1 : n⁻¹ * c * n ∈ Cen (b * b₁) := by
        have := conj_mem_cen (g := n⁻¹) hcb₁b₂
        rwa [show n⁻¹ * (b₁ * b₂) * n⁻¹⁻¹ = b * b₁ by
          calc n⁻¹ * (b₁ * b₂) * n⁻¹⁻¹ = (n⁻¹ * b₁ * n) * (n⁻¹ * b₂ * n) := by group
            _ = b * b₁ := by rw [hn'b, hn'b₁], inv_inv] at this
      have hc'2 : n⁻¹ * c * n ∈ Cen b₂ := by
        have := conj_mem_cen (g := n⁻¹) hcb
        rwa [inv_inv, hn'b₂] at this
      obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.1 hy
      refine Subgroup.mem_map.2 ⟨(n⁻¹ * c * n) * y * (n⁻¹ * c * n)⁻¹, Subgroup.mem_inf.2
        ⟨hYn _ hc'1 y hyY, ?_⟩, ?_⟩
      · have := conj_mem_cen (g := n⁻¹ * c * n) hyC
        have e : (n⁻¹ * c * n) * b₂ * (n⁻¹ * c * n)⁻¹ = b₂ := by
          have h0 := Subgroup.mem_centralizer_singleton_iff.1 hc'2
          calc (n⁻¹ * c * n) * b₂ * (n⁻¹ * c * n)⁻¹ = (b₂ * (n⁻¹ * c * n)) * (n⁻¹ * c * n)⁻¹ := by
                rw [h0]
            _ = b₂ := by group
        rwa [e] at this
      · simp [MulAut.conj_apply]
        group
  have hbot : (Y ⊓ Cen b₂).map (MulAut.conj n).toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    exact hW.trans (le_of_eq hX)
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have : (MulAut.conj n).toMonoidHom y ∈ (Y ⊓ Cen b₂).map (MulAut.conj n).toMonoidHom :=
    Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  have h1 : n * y * n⁻¹ = 1 := this
  have : y = 1 := by
    have := mul_inv_eq_one.1 h1
    exact mul_left_cancel (a := n) (by rw [this, mul_one])
  exact this

theorem S44_Y_trivial (hH : LemmaH) (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) (hZ : Subgroup.center L = ⊥) (hX : Opp 3 (Cen b) = ⊥)
    (hodd : Odd (Nat.card (Opp 3 (Cen (b * b₁))))) : Opp 3 (Cen (b * b₁)) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hK60, hKs⟩ := K_simple60 hA h hZ
  set Y := Opp 3 (Cen (b * b₁)) with hY
  have hCY := CY_b₂_trivial hA h hX hodd
  have hb₂K : b₂ ∈ K := h.hK.1
  have hKb : K ≤ Cen b := fun k hk => h.hyp.hLC ((Subgroup.mem_inf.1 (h.hK.2.2.1 ▸
    Subgroup.mem_sup_right hk : k ∈ L ⊓ Cen b₁)).1)
  have hKb₁ : K ≤ Cen b₁ := h.hK.2.2.2.2
  have hKD : K ≤ Cen (b * b₁) := by
    intro k hk
    have e1 := Subgroup.mem_centralizer_singleton_iff.1 (hKb hk)
    have e2 := Subgroup.mem_centralizer_singleton_iff.1 (hKb₁ hk)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    calc k * (b * b₁) = (k * b) * b₁ := by rw [mul_assoc]
      _ = (b * k) * b₁ := by rw [e1]
      _ = b * (k * b₁) := by rw [mul_assoc]
      _ = b * (b₁ * k) := by rw [e2]
      _ = (b * b₁) * k := by rw [mul_assoc]
  have hKY : K ≤ Nor Y := le_nor_Opp 3 hKD
  have hNbot : ∀ g : G, g ∈ Nor (⊥ : Subgroup G) := by
    intro g
    rw [Nor, Subgroup.mem_normalizer_iff]
    intro z
    simp only [Subgroup.mem_bot]
    constructor
    · intro hz; rw [hz]; group
    · intro hz
      have : g * z * g⁻¹ = 1 := hz
      have := mul_inv_eq_one.1 this
      exact mul_left_cancel (a := g) (by rw [this, mul_one])
  have hmain := hH G K Y ⊥ b₂ hK60 hKs (by
      rw [hY]
      exact fun h3 => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
        (FF79.L14.Opp_coprime 3 (Cen (b * b₁))) h3) hKY bot_le (fun k _ => hNbot k) (by
      rw [Subgroup.bot_subgroupOf]; infer_instance) hb₂K (orderOf_b₂ h) (by
      rintro u hu ⟨n', hn', hu'⟩
      rw [Subgroup.mem_bot] at hn'
      rw [hn', mul_one] at hu'
      have hc : u ∈ Cen b₂ := by
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have e : b₂ * u * b₂⁻¹ = u := hu'
        calc u * b₂ = (b₂ * u * b₂⁻¹) * b₂ := by rw [e]
          _ = b₂ * u := by group
      have : u ∈ Y ⊓ Cen b₂ := Subgroup.mem_inf.2 ⟨hu, hc⟩
      rw [hCY] at this
      exact this)
  obtain ⟨-, -, r, hr⟩ := hmain
  rw [Subgroup.card_bot, one_mul] at hr
  have hr0 : r = 0 := by
    by_contra hne
    have h2 : 2 ∣ Nat.card Y := by
      rw [hr]; exact dvd_pow (by norm_num) hne
    have := Nat.odd_iff.1 hodd
    omega
  rw [hr0, pow_zero] at hr
  exact Subgroup.card_eq_one.1 hr

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
