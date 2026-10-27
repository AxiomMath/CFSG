module

public import CFSG.Quasithin.Background.F918Z8a
public import CFSG.Quasithin.Background.F918Z8b
public import CFSG.Quasithin.Background.F918Z8c
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

section Counting

variable {W : Type} [CommGroup W]

theorem d321d_stabSub_inf {A : Subgroup (MulAut W)} {X K : Subgroup W} (hX : A ≤ stabSub X)
    (hK : A ≤ stabSub K) : A ≤ stabSub (X ⊓ K) := by
  intro g hg u
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX hg u, hK hg u]

theorem d321d_stabSub_sup {A : Subgroup (MulAut W)} {X K : Subgroup W} (hX : A ≤ stabSub X)
    (hK : A ≤ stabSub K) : A ≤ stabSub (X ⊔ K) := by
  rw [Z391.le_stabSub_iff]
  intro g hg y hy
  obtain ⟨x, hx, k, hk, rfl⟩ := Subgroup.mem_sup.mp hy
  rw [map_mul]
  exact Subgroup.mul_mem_sup ((hX hg x).2 hx) ((hK hg k).2 hk)

theorem d321d_stabSub_conj {E : Subgroup (MulAut W)} {N : Subgroup W} (g : MulAut W)
    (hE : E ≤ stabSub N) : conjAutSub g E ≤ stabSub (N.map g.toMonoidHom) := by
  rw [Z391.le_stabSub_iff]
  rintro x hx _ ⟨n, hn, rfl⟩
  have h1 : g⁻¹ * x * g ∈ E := mem_conjAutSub_iff.mp hx
  have h2 : x (g n) = g ((g⁻¹ * x * g) n) := by simp [MulAut.mul_apply]
  rw [MulEquiv.coe_toMonoidHom, h2]
  exact ⟨_, (hE h1 n).2 hn, rfl⟩

theorem d321d_mk_mem_fixV_autSec {A : Subgroup (MulAut W)} {N D : Subgroup W}
    (hAN : A ≤ stabSub N) (hAD : A ≤ stabSub D) (n : ↥N) :
    (QuotientGroup.mk n : Sec N D) ∈ fixV (autSec A N D) ↔ (n : W) ∈ commModSub N A D := by
  unfold autSec
  rw [mk_mem_fixV_autQuot]
  constructor
  · intro h
    refine ⟨n.2, fun g hg => ?_⟩
    have h1 := h (resHom N ⟨g, hAN hg⟩) (mem_autSub.mpr ⟨⟨g, hAN hg⟩, hg, rfl⟩)
      (autSub_le_stabSub_subgroupOf hAD (mem_autSub.mpr ⟨⟨g, hAN hg⟩, hg, rfl⟩))
    rw [Subgroup.mem_subgroupOf] at h1
    exact h1
  · rintro ⟨-, h⟩ g hg -
    obtain ⟨g', hg'A, rfl⟩ := mem_autSub.mp hg
    rw [Subgroup.mem_subgroupOf]
    exact h g' hg'A

theorem d321d_rk_fixV_autSec_add [Finite W] {A : Subgroup (MulAut W)} {N D : Subgroup W}
    (hDN : D ≤ N) (hAN : A ≤ stabSub N) (hAD : A ≤ stabSub D) :
    rk (fixV (autSec A N D)) + rk D = rk (commModSub N A D) := by
  set π : ↥N →* Sec N D := QuotientGroup.mk' (D.subgroupOf N) with hπ
  set K : Subgroup ↥N := (commModSub N A D).subgroupOf N with hK
  have hKeq : K = (fixV (autSec A N D)).comap π := by
    ext n
    rw [Subgroup.mem_comap, hK, Subgroup.mem_subgroupOf]
    exact (d321d_mk_mem_fixV_autSec hAN hAD n).symm
  have hmap : K.map π = fixV (autSec A N D) := by
    rw [hKeq]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hkerK : π.ker = D.subgroupOf N := by
    rw [hπ, QuotientGroup.ker_mk']
  have hker : π.ker ≤ K := by
    intro n hn
    rw [hkerK, Subgroup.mem_subgroupOf] at hn
    rw [hK, Subgroup.mem_subgroupOf]
    exact ⟨n.2, fun g hg => D.mul_mem ((hAD hg _).2 hn) (D.inv_mem hn)⟩
  have h1 := B1More.card_map_mul_card_inf_ker K π
  rw [hmap, inf_eq_right.mpr hker, hkerK] at h1
  have h2 : Nat.card ↥(D.subgroupOf N) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv
  have h3 : Nat.card ↥K = Nat.card ↥(commModSub N A D) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (commModSub_le N A D)).toEquiv
  rw [h2, h3] at h1
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h1]

theorem d321d_rkIdx_add_rk_commModSub [Finite W] {A : Subgroup (MulAut W)} {N D : Subgroup W}
    (hDN : D ≤ N) (hAN : A ≤ stabSub N) (hAD : A ≤ stabSub D) :
    rkIdx (fixV (autSec A N D)) + rk (commModSub N A D) = rk N := by
  have h1 := d321d_rk_fixV_autSec_add hDN hAN hAD
  have h2 := rk_add_rkIdx (fixV (autSec A N D))
  have h3 := B5.rk_sec_add hDN
  omega

theorem d321d_rkIdx_fixV_autSec_mono [Finite W] {B A : Subgroup (MulAut W)} {N D : Subgroup W}
    (hBA : B ≤ A) (hDN : D ≤ N) (hAN : A ≤ stabSub N) (hAD : A ≤ stabSub D) :
    rkIdx (fixV (autSec B N D)) ≤ rkIdx (fixV (autSec A N D)) := by
  have h1 := d321d_rkIdx_add_rk_commModSub hDN (hBA.trans hAN) (hBA.trans hAD)
  have h2 := d321d_rkIdx_add_rk_commModSub hDN hAN hAD
  have h3 : rk (commModSub N A D) ≤ rk (commModSub N B D) :=
    rk_mono fun _ h => ⟨h.1, fun g hg => h.2 g (hBA hg)⟩
  omega

theorem d321d_commModSub_map (g : MulAut W) (E : Subgroup (MulAut W)) (N D : Subgroup W) :
    commModSub (N.map g.toMonoidHom) (conjAutSub g E) (D.map g.toMonoidHom) =
      (commModSub N E D).map g.toMonoidHom := by
  ext n'
  constructor
  · rintro ⟨⟨n, hn, rfl⟩, h⟩
    refine ⟨n, ⟨hn, fun e he => ?_⟩, rfl⟩
    have h1 : g * e * g⁻¹ ∈ conjAutSub g E := by
      rw [mem_conjAutSub_iff]
      have e0 : g⁻¹ * (g * e * g⁻¹) * g = e := by group
      rw [e0]
      exact he
    have h2 := h _ h1
    have e1 : (g * e * g⁻¹) (g n) * (g n)⁻¹ = g (e n * n⁻¹) := by
      simp [MulAut.mul_apply]
    rw [MulEquiv.coe_toMonoidHom, e1] at h2
    exact (Subgroup.mem_map_iff_mem (f := g.toMonoidHom) g.injective).mp h2
  · rintro ⟨n, ⟨hn, h⟩, rfl⟩
    refine ⟨⟨n, hn, rfl⟩, fun e' he' => ?_⟩
    have h1 : g⁻¹ * e' * g ∈ E := mem_conjAutSub_iff.mp he'
    have e1 : e' (g n) * (g n)⁻¹ = g (((g⁻¹ * e' * g) n) * n⁻¹) := by
      simp [MulAut.mul_apply]
    rw [MulEquiv.coe_toMonoidHom, e1]
    exact ⟨_, h _ h1, rfl⟩

theorem d321d_rkIdx_fixV_autSec_conj [Finite W] (g : MulAut W) {E : Subgroup (MulAut W)}
    {N D : Subgroup W} (hDN : D ≤ N) (hEN : E ≤ stabSub N) (hED : E ≤ stabSub D) :
    rkIdx (fixV (autSec (conjAutSub g E) (N.map g.toMonoidHom) (D.map g.toMonoidHom))) =
      rkIdx (fixV (autSec E N D)) := by
  have h1 := d321d_rkIdx_add_rk_commModSub (Subgroup.map_mono (f := g.toMonoidHom) hDN)
    (d321d_stabSub_conj g hEN) (d321d_stabSub_conj g hED)
  have h2 := d321d_rkIdx_add_rk_commModSub hDN hEN hED
  rw [d321d_commModSub_map, rk_map_aut, rk_map_aut] at h1
  omega

theorem d321d_commModSub_sup {A : Subgroup (MulAut W)} {X K : Subgroup W} (hX : A ≤ stabSub X)
    (hK : A ≤ stabSub K) :
    commModSub (X ⊔ K) A K = commModSub X A (X ⊓ K) ⊔ K := by
  apply le_antisymm
  · rintro p ⟨hp, hpA⟩
    obtain ⟨x, hx, k, hk, rfl⟩ := Subgroup.mem_sup.mp hp
    refine Subgroup.mul_mem_sup ⟨hx, fun g hg => ⟨?_, ?_⟩⟩ hk
    · exact X.mul_mem ((hX hg x).2 hx) (X.inv_mem hx)
    · have h1 := hpA g hg
      have h2 : g k * k⁻¹ ∈ K := K.mul_mem ((hK hg k).2 hk) (K.inv_mem hk)
      have e : g x * x⁻¹ = (g (x * k) * (x * k)⁻¹) * (g k * k⁻¹)⁻¹ := by
        rw [map_mul]
        simp only [mul_inv_rev, inv_inv]
        rw [mul_comm (g x) (g k)]
        rw [show g k * g x * (k⁻¹ * x⁻¹) * (k * (g k)⁻¹) =
          g x * x⁻¹ * (g k * (g k)⁻¹) * (k⁻¹ * k) by ac_rfl]
        simp
      rw [e]
      exact K.mul_mem h1 (K.inv_mem h2)
  · refine sup_le ?_ ?_
    · rintro x ⟨hx, hxA⟩
      exact ⟨Subgroup.mem_sup_left hx, fun g hg => (hxA g hg).2⟩
    · intro k hk
      exact ⟨Subgroup.mem_sup_right hk,
        fun g hg => K.mul_mem ((hK hg k).2 hk) (K.inv_mem hk)⟩

theorem d321d_rkIdx_fixV_autSec_sup [Finite W] {A : Subgroup (MulAut W)} {X K : Subgroup W}
    (hX : A ≤ stabSub X) (hK : A ≤ stabSub K) :
    rkIdx (fixV (autSec A (X ⊔ K) K)) = rkIdx (fixV (autSec A X (X ⊓ K))) := by
  have hXK : A ≤ stabSub (X ⊓ K) := d321d_stabSub_inf hX hK
  have h1 := d321d_rkIdx_add_rk_commModSub (le_sup_right : K ≤ X ⊔ K) (d321d_stabSub_sup hX hK) hK
  have h2 := d321d_rkIdx_add_rk_commModSub (inf_le_left : X ⊓ K ≤ X) hX hXK
  have h3 := rk_sup_add_rk_inf (commModSub X A (X ⊓ K)) K
  have h4 : commModSub X A (X ⊓ K) ⊓ K = X ⊓ K := by
    apply le_antisymm
    · exact inf_le_inf_right _ (commModSub_le X A (X ⊓ K))
    · refine le_inf (fun x hx => ⟨hx.1, fun g hg => ?_⟩) inf_le_right
      exact (X ⊓ K).mul_mem ((hXK hg x).2 hx) ((X ⊓ K).inv_mem hx)
  have h5 := rk_sup_add_rk_inf X K
  rw [h4, ← d321d_commModSub_sup hX hK] at h3
  omega

theorem d321d_split_count [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    {U U' C : Subgroup W} (hsum : U ⊔ U' ⊔ C = ⊤) (hint : (U ⊔ C) ⊓ (U' ⊔ C) ≤ C)
    (hAU : A ≤ stabSub U) (hAU' : A ≤ stabSub U') (hAC : A ≤ stabSub C) :
    rkIdx (fixV (autSec A U (U ⊓ C))) + rkIdx (fixV (autSec A U' (U' ⊓ C))) ≤
      rkIdx (fixV A) := by
  have hUC : A ≤ stabSub (U ⊔ C) := d321d_stabSub_sup hAU hAC
  have hAtop : A ≤ stabSub (⊤ : Subgroup W) := fun g _ u => by simp
  have h1 := B5.rkIdx_chain hexp (inf_le_left : U ⊓ C ≤ U) (le_sup_left : U ≤ U ⊔ C)
    (le_top : U ⊔ C ≤ ⊤) hAU hAtop hUC
  have h2 := d321d_rkIdx_fixV_autSec_sup hAU' hUC
  have e1 : U' ⊔ (U ⊔ C) = ⊤ := by
    rw [← hsum, sup_comm U U', sup_assoc]
  have e2 : U' ⊓ (U ⊔ C) = U' ⊓ C := by
    apply le_antisymm
    · exact le_inf inf_le_left (fun x hx => hint ⟨hx.2, Subgroup.mem_sup_left hx.1⟩)
    · exact inf_le_inf_left _ le_sup_right
  rw [e1, e2] at h2
  omega

theorem d321d_swap_count [Finite W] {A₀ : Subgroup (MulAut W)} {U C : Subgroup W} {a : MulAut W}
    (ha : a * a = 1) (hcomm : ∀ g ∈ A₀, g * a = a * g) (hAU : A₀ ≤ stabSub U)
    (hAC : A₀ ≤ stabSub C) (haC : C.map a.toMonoidHom = C)
    (hsum : U ⊔ U.map a.toMonoidHom ⊔ C = ⊤)
    (hint : (U ⊔ C) ⊓ (U.map a.toMonoidHom ⊔ C) ≤ C) :
    rk (Sec U (U ⊓ C)) + rkIdx (fixV (autSec A₀ U (U ⊓ C))) ≤
      rkIdx (fixV (A₀ ⊔ Subgroup.zpowers a)) := by
  have hmapP : (U ⊔ C).map a.toMonoidHom = U.map a.toMonoidHom ⊔ C := by
    rw [Subgroup.map_sup, haC]
  have hsumP : (U ⊔ C) ⊔ (U ⊔ C).map a.toMonoidHom = ⊤ := by
    rw [hmapP]
    apply top_le_iff.mp
    rw [← hsum]
    exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
      (le_sup_right.trans le_sup_left)
  have hinterP : (U ⊔ C) ⊓ (U ⊔ C).map a.toMonoidHom = C := by
    apply le_antisymm
    · rw [hmapP]
      exact hint
    · exact le_inf (le_sup_right : C ≤ U ⊔ C) (by rw [hmapP]; exact le_sup_right)
  have hAP : A₀ ≤ stabSub (U ⊔ C) := d321d_stabSub_sup hAU hAC
  have h1 := rk_fixV_swap_le ha hcomm hAP hsumP
  have h2 := rk_sup_swap_add_rk_inf hsumP
  rw [hinterP] at h1 h2
  have h3 := d321d_rkIdx_add_rk_commModSub (inf_le_left : U ⊓ C ≤ U) hAU
    (d321d_stabSub_inf hAU hAC)
  have h4 := rk_sup_add_rk_inf (commModSub U A₀ (U ⊓ C)) C
  have h5 : commModSub U A₀ (U ⊓ C) ⊓ C = U ⊓ C := by
    apply le_antisymm
    · exact inf_le_inf_right _ (commModSub_le U A₀ (U ⊓ C))
    · refine le_inf (fun x hx => ⟨hx.1, fun g hg => ?_⟩) inf_le_right
      exact (U ⊓ C).mul_mem ((d321d_stabSub_inf hAU hAC hg x).2 hx)
        ((U ⊓ C).inv_mem hx)
  rw [h5, ← d321d_commModSub_sup hAU hAC] at h4
  have h6 := rk_sup_add_rk_inf U C
  have h7 := B5.rk_sec_add (inf_le_left : U ⊓ C ≤ U)
  have h8 := rk_add_rkIdx (fixV (A₀ ⊔ Subgroup.zpowers a))
  rw [fixV_sup_eq_inf_fixV] at h8 ⊢
  have h9 : rk ↥(C ⊓ fixV A₀) ≤ rk ↥C := rk_mono inf_le_left
  omega

end Counting

section Perfect

variable {W : Type} [CommGroup W]

theorem d321d_perfect_map {G H : Type*} [Group G] [Group H] (f : G →* H) {P : Subgroup G}
    (hP : ⁅P, P⁆ = P) : ⁅P.map f, P.map f⁆ = P.map f := by
  rw [← Subgroup.map_commutator, hP]

theorem d321d_perfect_subgroupOf {G : Type*} [Group G] {P S : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPS : P ≤ S) : ⁅P.subgroupOf S, P.subgroupOf S⁆ = P.subgroupOf S := by
  apply Subgroup.map_injective S.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPS, hP]

theorem d321d_perfect_autSec {L : Subgroup (MulAut W)} {U Z : Subgroup W} (hperf : ⁅L, L⁆ = L)
    (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z) :
    ⁅autSec L U Z, autSec L U Z⁆ = autSec L U Z := by
  have h1 : ⁅autSub L U, autSub L U⁆ = autSub L U :=
    d321d_perfect_map (resHom U) (d321d_perfect_subgroupOf hperf hLU)
  have h2 : autSub L U ≤ stabSub (Z.subgroupOf U) := autSub_le_stabSub_subgroupOf hLZ
  exact d321d_perfect_map (quotHom (Z.subgroupOf U)) (d321d_perfect_subgroupOf h1 h2)

theorem d321d_solvable_mulAut {S : Type} [Group S] [Finite S] (h : Nat.card S ≤ 4) :
    Group.IsSolvable (MulAut S) := by
  have : Group.IsSolvable (Equiv.Perm S) := Equiv.Perm.isSolvable h
  refine Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm S) ?_
  intro f g hfg
  exact MulEquiv.ext fun x => congrArg (fun p : Equiv.Perm S => p x) hfg

theorem d321d_three_le_rk_sec [Finite W] (hexp : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} (hperf : ⁅L, L⁆ = L) (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    (hnt : ¬ L ≤ centSec U Z) : 3 ≤ rk (Sec U Z) := by
  by_contra hlt
  have hcard : Nat.card (Sec U Z) ≤ 4 := by
    rw [B5.card_sec_eq_two_pow hexp U Z]
    calc 2 ^ rk (Sec U Z) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have hsolv : Group.IsSolvable (MulAut (Sec U Z)) := d321d_solvable_mulAut hcard
  have hX : Group.IsSolvable ↥(autSec L U Z) :=
    Group.isSolvable_of_isSolvable_injective (f := (autSec L U Z).subtype)
      (autSec L U Z).subtype_injective
  have hbot : autSec L U Z ≠ ⊥ := Bridge.autSec_ne_bot (le_inf hLU hLZ) hnt
  have : Nontrivial ↥(autSec L U Z) := (Subgroup.nontrivial_iff_ne_bot _).mpr hbot
  have : Group.IsPerfect ↥(autSec L U Z) :=
    Subgroup.isPerfect_iff.2 (d321d_perfect_autSec hperf hLU hLZ)
  exact Group.IsPerfect.not_isSolvable _ hX

end Perfect

section Situation

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

omit [Finite W] in
theorem d321d_le_stabSub_fixV {X : Subgroup (MulAut W)}
    (h : X ≤ Subgroup.normalizer (Mp : Set (MulAut W))) : X ≤ stabSub (fixV Mp) := by
  rw [Z391.le_stabSub_iff]
  intro g hg c hc x hx
  have hx' : g⁻¹ * x * g ∈ Mp := (Subgroup.mem_normalizer_iff''.mp (h hg) x).mp hx
  have e : x (g c) = g ((g⁻¹ * x * g) c) := by simp [MulAut.mul_apply]
  rw [e, hc _ hx']

omit [Finite W] in
theorem d321d_le_stabSub_commV {X : Subgroup (MulAut W)}
    (h : X ≤ Subgroup.normalizer (L : Set (MulAut W))) : X ≤ stabSub (commV L) :=
  d321a_le_stabSub_of_inv fun _ hx _ hu => d321a_commV_stable (h hx) hu

omit [Finite W] in
theorem d321d_map_fixV {g : MulAut W} (hg : g ∈ Subgroup.normalizer (Mp : Set (MulAut W))) :
    (fixV Mp).map g.toMonoidHom = fixV Mp := by
  apply map_eq_of_mem_stabSub
  exact d321d_le_stabSub_fixV (Subgroup.zpowers_le.mpr hg) (Subgroup.mem_zpowers g)

theorem d321d_perm (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) :
    ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L := by
  obtain ⟨hA38, hcomm, -, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hLs : IsSimpleGroup ↥L := Vol2Native.L122A.isSimpleGroup_of_a38Types hA38
  have hD := hstd.hyp
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hD.quasi.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a', b', fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  exact fun g hg => d321a_perm hLs hnab hcomm hMp hD.Mp_normal hg

omit [Finite W] in
theorem d321d_normalizes_conj
    (hperm : ∀ g ∈ M, conjAutSub g L = L ∨ conjAutSub g L = conjAutSub t L) (htM : t ∈ M)
    (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W))) {m : MulAut W}
    (hm : m ∈ M) (hmL : conjAutSub m L = L) :
    conjAutSub m (conjAutSub t L) = conjAutSub t L := by
  rcases hperm (m * t) (M.mul_mem hm htM) with h | h
  · exfalso
    apply htL
    rw [d321a_conjAutSub_mul] at h
    exact d321a_mem_normalizer_iff.mpr (d321a_conjAutSub_inj (h.trans hmL.symm))
  · rwa [d321a_conjAutSub_mul] at h

theorem d321d_commV_ne_bot (hstd : D3Std M Mp T L V) (hMp : Mp = L ⊔ conjAutSub t L)
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) : commV L ≠ ⊥ := by
  intro h
  have hVL := d321_comm_eq hstd hMp htriv
  have hVU : V ≤ commV L := by
    calc V = commSub V L := hVL.symm
      _ ≤ commSub ⊤ L := commSub_mono le_top le_rfl
      _ = commV L := (commV_eq_commSub L).symm
  obtain ⟨-, -, hVlt, -⟩ := mem_irrPlus_top_iff.1 hstd.hyp.irr
  have hV0 : V = ⊥ := le_bot_iff.1 (hVU.trans h.le)
  rw [hV0, bot_inf_eq] at hVlt
  exact lt_irrefl _ hVlt

omit [Finite W] in
theorem d321d_not_le_centSec_top {K : Subgroup (MulAut W)} (hperf : ⁅K, K⁆ = K) (hKM : K ≤ Mp)
    (hne : commV K ≠ ⊥) : ¬ K ≤ centSec ⊤ (fixV Mp) := by
  intro h
  apply hne
  have h1 : commV K ≤ fixV Mp := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    exact (h hx).2 v trivial
  have h2 : commV K ≤ fixV K := h1.trans (fixV_anti hKM)
  have h3 : commSub (commV K) K = ⊥ := commSub_eq_bot_iff.mpr h2
  rw [B5.commSub_commV_eq hperf] at h3
  exact h3

omit [Finite W] in
theorem d321d_not_le_centSec_sec {K : Subgroup (MulAut W)} (hperf : ⁅K, K⁆ = K) (hKM : K ≤ Mp)
    (hne : commV K ≠ ⊥) : ¬ K ≤ centSec (commV K) (commV K ⊓ fixV Mp) := by
  intro h
  apply hne
  have h1 : commSub (commV K) K ≤ fixV Mp := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, hv, rfl⟩
    exact ((h hx).2 v hv).2
  have h2 : commSub (commV K) K ≤ fixV K := h1.trans (fixV_anti hKM)
  have h3 : commSub (commSub (commV K) K) K = ⊥ := commSub_eq_bot_iff.mpr h2
  rw [B5.commSub_commV_eq hperf, B5.commSub_commV_eq hperf] at h3
  exact h3

theorem d321d_faithful_top (hL38 : D3L38)
    (hstd : D3Std M Mp T L V) (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    {B : Subgroup (MulAut W)} (hBT : B ≤ T)
    (hBf : ∀ b ∈ B, (∀ x ∈ Mp, b * x = x * b) → b = 1) : B ⊓ centSec ⊤ (fixV Mp) = ⊥ := by
  have hD := hstd.hyp
  obtain ⟨-, hcomm, -, -⟩ := hL38 W M Mp T L V hstd t htT htL hMp
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hD.sylow.1.trans hD.Mp_normal
  have hGN : Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hTn
  have hN : ∀ g ∈ Mp ⊔ T, ∀ l ∈ Mp, g * l * g⁻¹ ∈ Mp := fun g hg l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hGN hg)) l).1 hl
  have hGtop : Mp ⊔ T ≤ stabSub (⊤ : Subgroup W) := fun g _ u => by simp
  have hGC : Mp ⊔ T ≤ stabSub (fixV Mp) := d321d_le_stabSub_fixV hGN
  have hqL : CFSG.IsQuasisimple ↥L := hD.quasi
  have hqLt : CFSG.IsQuasisimple ↥(conjAutSub t L) := (hD.conj htT).quasi
  have hperfL : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hqL.1
    exact Subgroup.commutator_eq_self
  have hperfLt : ⁅conjAutSub t L, conjAutSub t L⁆ = conjAutSub t L := by
    have : Group.IsPerfect ↥(conjAutSub t L) := hqLt.1
    exact Subgroup.commutator_eq_self
  have hperf : ⁅Mp, Mp⁆ = Mp := by
    rw [hMp]
    exact d391ll_perfect_sup hperfL hperfLt
  have hcomm' : ∀ x ∈ L, ∀ y ∈ conjAutSub t L, x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_le.1 hcomm.le x hx y hy
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  have hne : commV L ≠ ⊥ := d321d_commV_ne_bot hstd hMp htriv
  have hne' : commV (conjAutSub t L) ≠ ⊥ := by
    rw [d321b_commV_conjAutSub]
    intro h
    exact hne ((Subgroup.map_eq_bot_iff_of_injective _ t.injective).mp h)
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hLtMp : conjAutSub t L ≤ Mp := by
    rw [hMp]
    exact le_sup_right
  have hLnot : ¬ L ≤ centSec ⊤ (fixV Mp) := d321d_not_le_centSec_top hperfL hLMp hne
  have hLtnot : ¬ conjAutSub t L ≤ centSec ⊤ (fixV Mp) :=
    d321d_not_le_centSec_top hperfLt hLtMp hne'
  have hkc := d391ll_kernel_central hMp hqL hqLt hcomm'
    (fun g hg c hc => conj_mem_centSec (hGtop (Subgroup.mem_sup_left hg))
      (hGC (Subgroup.mem_sup_left hg)) hc)
    hLnot hLtnot
  exact d391ll_inf_centSec_eq_bot hperf le_sup_left (hBT.trans le_sup_right) hN hGtop hGC hkc hBf

omit [Finite W] in
theorem d321d_centSec_top {U U' C : Subgroup W} (hsum : U ⊔ U' ⊔ C = ⊤) {b : MulAut W}
    (hbC : b ∈ stabSub C) (hb : b ∈ centSec U (U ⊓ C)) (hb' : b ∈ centSec U' (U' ⊓ C)) :
    b ∈ centSec ⊤ C := by
  refine ⟨fun u => by simp, fun w _ => ?_⟩
  have hw : w ∈ U ⊔ U' ⊔ C := by rw [hsum]; exact Subgroup.mem_top w
  obtain ⟨y, hy, c, hc, rfl⟩ := Subgroup.mem_sup.mp hw
  obtain ⟨u, hu, u', hu', rfl⟩ := Subgroup.mem_sup.mp hy
  have e : b (u * u' * c) * (u * u' * c)⁻¹ = (b u * u⁻¹) * (b u' * u'⁻¹) * (b c * c⁻¹) := by
    rw [map_mul, map_mul]
    simp only [mul_inv_rev]
    ac_rfl
  rw [e]
  exact C.mul_mem (C.mul_mem (hb.2 u hu).2 (hb'.2 u' hu').2)
    (C.mul_mem ((hbC c).2 hc) (C.inv_mem hc))

omit [Finite W] in
theorem d321d_mem_centSec_conj {g e : MulAut W} {N D : Subgroup W} (he : e ∈ centSec N D) :
    g * e * g⁻¹ ∈ centSec (N.map g.toMonoidHom) (D.map g.toMonoidHom) := by
  obtain ⟨hs, h⟩ := he
  refine ⟨fun u => ?_, fun w hw => ?_⟩
  · rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have e1 : g.symm ((g * e * g⁻¹) u) = e (g⁻¹ u) := by simp [MulAut.mul_apply]
    have e2 : g.symm u = g⁻¹ u := rfl
    rw [e1, e2]
    exact hs (g⁻¹ u)
  · obtain ⟨n, hn, rfl⟩ := hw
    have e1 : (g * e * g⁻¹) (g n) * (g n)⁻¹ = g (e n * n⁻¹) := by simp [MulAut.mul_apply]
    rw [MulEquiv.coe_toMonoidHom, e1]
    exact ⟨_, h n hn, rfl⟩

end Situation

section Offender

variable {W : Type} [CommGroup W]

omit [CommGroup W] in
theorem d321d_isElemAbelian2_mono {V : Type*} [CommGroup V] {B A : Subgroup (MulAut V)}
    (hA : IsElemAbelian2 A) (hBA : B ≤ A) : IsElemAbelian2 B :=
  ⟨fun a ha b hb => hA.1 a (hBA ha) b (hBA hb), fun a ha => hA.2 a (hBA ha)⟩

theorem d321d_isElemAbelian2_conj (g : MulAut W) {A : Subgroup (MulAut W)}
    (hA : IsElemAbelian2 A) : IsElemAbelian2 (conjAutSub g A) := by
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h1 := hA.1 _ (mem_conjAutSub_iff.mp hx) _ (mem_conjAutSub_iff.mp hy)
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = y * x := by group
  · have h1 := hA.2 _ (mem_conjAutSub_iff.mp hx)
    calc x ^ 2 = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [pow_two]; group
      _ = 1 := by rw [← pow_two, h1]; group

theorem d321d_rk_conj (g : MulAut W) (X : Subgroup (MulAut W)) :
    rk ↥(conjAutSub g X) = rk ↥X := by
  unfold rk
  rw [d321a_card_conjAutSub]

variable [Finite W]

theorem d321d_rk_le_rk_add_one {A A₀ : Subgroup (MulAut W)} {a : MulAut W}
    (hA : IsElemAbelian2 A) (hA₀ : A₀ ≤ A) (hsplit : ∀ g ∈ A, g ∈ A₀ ∨ a⁻¹ * g ∈ A₀)
    (haA : a ∈ A) : rk ↥A ≤ rk ↥A₀ + 1 := by
  have hA₀e : IsElemAbelian2 A₀ := d321d_isElemAbelian2_mono hA hA₀
  have hidx : (A₀.subgroupOf A).index ≤ 2 := by
    have hsurj : Function.Surjective (fun b : Bool => if b then
        (QuotientGroup.mk (⟨a, haA⟩ : ↥A) : ↥A ⧸ A₀.subgroupOf A)
        else (QuotientGroup.mk (1 : ↥A) : ↥A ⧸ A₀.subgroupOf A)) := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rcases hsplit g g.2 with h | h
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf] using A₀.inv_mem h
      · refine ⟨true, ?_⟩
        simp only [ite_true]
        rw [QuotientGroup.eq]
        simpa [Subgroup.mem_subgroupOf] using h
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa [Subgroup.index, Nat.card_eq_fintype_card] using this
  have h1 := Subgroup.card_mul_index (A₀.subgroupOf A)
  have h2 : Nat.card ↥(A₀.subgroupOf A) = Nat.card ↥A₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀).toEquiv
  rw [h2] at h1
  have h3 : Nat.card ↥A ≤ Nat.card ↥A₀ * 2 := h1 ▸ Nat.mul_le_mul_left _ hidx
  rw [card_eq_two_pow_of_isPGroup hA.isPGroup, card_eq_two_pow_of_isPGroup hA₀e.isPGroup,
    ← pow_succ] at h3
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3

theorem d321d_final {ML E : Subgroup (MulAut W)} {U Z : Subgroup W} (hE : IsA2 ML E)
    (hE3 : commSeries E 3 = ⊥) (hEU : E ≤ stabSub U) (hEZ : E ≤ stabSub Z)
    (hnt : ¬ E ≤ centSec U Z)
    (hr : rkIdx (fixV (autSec E U Z)) + 2 * rk ↥(E ⊓ centSec U Z) ≤ 2 * rk ↥E) :
    qhatOf (autSec ML U Z) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hAs : E ≤ stabSub U ⊓ stabSub Z := le_inf hEU hEZ
  have hA2 : IsA2 (autSec ML U Z) (autSec E U Z) :=
    ⟨autSec_mono hE.1 U Z, Bridge.autSec_ne_bot hAs hnt, Bridge.isElemAbelian2_autSec hE.2.2 hAs⟩
  refine kq_le_iff.mpr ⟨autSec E U Z, hA2, Z391.commSeries_autSec_eq_bot hEU hE3, ?_⟩
  have h1 := card_autSec_mul hEU hEZ
  have hrk : rk ↥(autSec E U Z) + rk ↥(E ⊓ centSec U Z) = rk ↥E := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h1]
  have hpos : 0 < rk ↥(autSec E U Z) := hA2.rk_pos
  unfold rAV
  rw [div_le_iff₀ (by exact_mod_cast hpos)]
  exact_mod_cast (by omega : rkIdx (fixV (autSec E U Z)) ≤ 2 * rk ↥(autSec E U Z))

end Offender

section Cases

variable {W : Type} [CommGroup W] [Finite W] {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
  {t : MulAut W}

theorem d321d_case_swap (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) {A : Subgroup (MulAut W)} (hA : QOff Mp T A (orbSup T V))
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hAL : ¬ A ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    qhatOf (autSec (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L)
      (commV L ⊓ fixV Mp)) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hD := hstd.hyp
  have hexp := hD.exp
  have hTM : T ≤ M := hD.sylow.1
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hTM.trans hD.Mp_normal
  have hAM : A ≤ M := hA.le.trans hTM
  have hperm := d321d_perm hL38 hstd htT htL hMp
  obtain ⟨hsplit, -⟩ := d321_struct hL38 hstd htT htL hMp htriv
  obtain ⟨a, haA, haL⟩ : ∃ a ∈ A, a ∉ Subgroup.normalizer (L : Set (MulAut W)) := by
    by_contra hcon
    push Not at hcon
    exact hAL fun g hg => hcon g hg
  have haconj : conjAutSub a L = conjAutSub t L :=
    (hperm a (hAM haA)).resolve_left fun h => haL (d321a_mem_normalizer_iff.mpr h)
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Subgroup (MulAut W),
      A₀ = A ⊓ Subgroup.normalizer (L : Set (MulAut W)) := ⟨_, rfl⟩
  have hmem : ∀ g, g ∈ A₀ ↔ g ∈ A ∧ g ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    fun g => by rw [hA₀]; exact Subgroup.mem_inf
  have hA₀A : A₀ ≤ A := fun g hg => ((hmem g).mp hg).1
  have hA₀N : A₀ ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun g hg => ((hmem g).mp hg).2
  have haa : a * a = 1 := by simpa [pow_two] using hA.elem.2 a haA
  have hcomm : ∀ g ∈ A₀, g * a = a * g := fun g hg => hA.elem.1 g (hA₀A hg) a haA
  have hsplitA : ∀ g ∈ A, g ∈ A₀ ∨ a⁻¹ * g ∈ A₀ := by
    intro g hg
    by_cases hgL : g ∈ Subgroup.normalizer (L : Set (MulAut W))
    · exact Or.inl ((hmem g).mpr ⟨hg, hgL⟩)
    · right
      have hgconj : conjAutSub g L = conjAutSub t L :=
        (hperm g (hAM hg)).resolve_left fun h => hgL (d321a_mem_normalizer_iff.mpr h)
      refine (hmem _).mpr ⟨A.mul_mem (A.inv_mem haA) hg, d321a_mem_normalizer_iff.mpr ?_⟩
      rw [d321a_conjAutSub_mul, hgconj, ← haconj, conjAutSub_inv_conjAutSub]
  have hAeq : A = A₀ ⊔ Subgroup.zpowers a := by
    apply le_antisymm
    · intro g hg
      rcases hsplitA g hg with h | h
      · exact Subgroup.mem_sup_left h
      · have e : g = a * (a⁻¹ * g) := by group
        rw [e, sup_comm]
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) h
    · exact sup_le hA₀A (Subgroup.zpowers_le.mpr haA)
  have hrkA : rk ↥A ≤ rk ↥A₀ + 1 := d321d_rk_le_rk_add_one hA.elem hA₀A hsplitA haA
  have hAU : A₀ ≤ stabSub (commV L) := d321d_le_stabSub_commV hA₀N
  have hAC : A₀ ≤ stabSub (fixV Mp) := d321d_le_stabSub_fixV ((hA₀A.trans hA.le).trans hTn)
  have haC : (fixV Mp).map a.toMonoidHom = fixV Mp := d321d_map_fixV (hTn (hA.le haA))
  have hUa : (commV L).map a.toMonoidHom = (commV L).map t.toMonoidHom := by
    have h1 := d321b_commV_conjAutSub a L
    rw [haconj, d321b_commV_conjAutSub] at h1
    exact h1.symm
  have hsumU : commV L ⊔ (commV L).map a.toMonoidHom ⊔ fixV Mp = ⊤ := by
    rw [hUa]
    exact hsplit.1.symm
  have hintU : (commV L ⊔ fixV Mp) ⊓ ((commV L).map a.toMonoidHom ⊔ fixV Mp) ≤ fixV Mp := by
    rw [hUa]
    exact hsplit.2
  have hcount := d321d_swap_count haa hcomm hAU hAC haC hsumU hintU
  rw [← hAeq] at hcount
  have hperfL : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hD.quasi.1
    exact Subgroup.commutator_eq_self
  have hLMp : L ≤ Mp := by
    rw [hMp]
    exact le_sup_left
  have hLU : L ≤ stabSub (commV L) := d321d_le_stabSub_commV Subgroup.le_normalizer
  have hLC : L ≤ stabSub (fixV Mp) :=
    d321d_le_stabSub_fixV (hLMp.trans Subgroup.le_normalizer)
  have hne : commV L ≠ ⊥ := d321d_commV_ne_bot hstd hMp htriv
  have h3 : 3 ≤ rk (Sec (commV L) (commV L ⊓ fixV Mp)) :=
    d321d_three_le_rk_sec hexp hperfL hLU (d321d_stabSub_inf hLU hLC)
      (d321d_not_le_centSec_sec hperfL hLMp hne)
  have hrA : 0 < rk ↥A := hA.elem.rk_pos hA.ne
  have hrat : rkIdx (fixV A) ≤ 2 * rk ↥A := by
    have h := hA.rat
    unfold rAV at h
    have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA
    rw [div_le_iff₀ hpos] at h
    exact_mod_cast h
  have hf : A₀ ⊓ centSec (commV L) (commV L ⊓ fixV Mp) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxA : x ∈ A := hA₀A hx.1
    have hxc : x ∈ centSec (commV L) (commV L ⊓ fixV Mp) := hx.2
    have hxa := d321d_mem_centSec_conj (g := a) hxc
    have e : a * x * a⁻¹ = x := by
      rw [mul_inv_eq_iff_eq_mul]
      exact hA.elem.1 a haA x hxA
    rw [e, Subgroup.map_inf _ _ _ a.injective, haC] at hxa
    have hxC : x ∈ stabSub (fixV Mp) := hAC hx.1
    have hxtop := d321d_centSec_top hsumU hxC hxc hxa
    have hbot := d321d_faithful_top hL38 hstd htT htL hMp htriv (B := A₀) (hA₀A.trans hA.le)
      (fun b hb h => hA.faithMp b (hA₀A hb) h)
    have : x ∈ A₀ ⊓ centSec ⊤ (fixV Mp) := ⟨hx.1, hxtop⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hrk0 : 1 ≤ rk ↥A₀ := by
    by_contra h0
    omega
  have hA₀ne : A₀ ≠ ⊥ := by
    intro h0
    rw [h0, rk_bot] at hrk0
    omega
  have hZ : A₀ ≤ stabSub (commV L ⊓ fixV Mp) := d321d_stabSub_inf hAU hAC
  refine d321d_final (E := A₀) ⟨le_inf (hA₀A.trans hAM) hA₀N, hA₀ne,
    d321d_isElemAbelian2_mono hA.elem hA₀A⟩
    (le_bot_iff.1 ((commSeries_mono hA₀A 3).trans
      (commSeries_eq_bot_of_le (by norm_num) hA.quad).le)) hAU hZ
    (fun h => hA₀ne (by rw [← hf]; exact (inf_eq_left.2 h).symm)) ?_
  rw [hf, rk_bot]
  omega

theorem d321d_case_normalizer (hL38 : D3L38)
    (hstd : D3Std M Mp T L V) (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) {A : Subgroup (MulAut W)} (hA : QOff Mp T A (orbSup T V))
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    qhatOf (autSec (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L)
      (commV L ⊓ fixV Mp)) ≤ ((2 : ℚ) : WithTop ℚ) := by
  have hD := hstd.hyp
  have hexp := hD.exp
  have hTM : T ≤ M := hD.sylow.1
  have htM : t ∈ M := hTM htT
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hTM.trans hD.Mp_normal
  have hAM : A ≤ M := hA.le.trans hTM
  have hperm := d321d_perm hL38 hstd htT htL hMp
  obtain ⟨hsplit, -⟩ := d321_struct hL38 hstd htT htL hMp htriv
  obtain ⟨U', hU'⟩ : ∃ U' : Subgroup W, U' = (commV L).map t.toMonoidHom := ⟨_, rfl⟩
  rw [← hU'] at hsplit
  have hALt : A ≤ Subgroup.normalizer ((conjAutSub t L : Subgroup (MulAut W)) : Set (MulAut W)) :=
    fun g hg => d321a_mem_normalizer_iff.mpr (d321d_normalizes_conj hperm htM htL (hAM hg)
      (d321a_mem_normalizer_iff.mp (hAL hg)))
  have hAU : A ≤ stabSub (commV L) := d321d_le_stabSub_commV hAL
  have hAU' : A ≤ stabSub U' := by
    have h := d321d_le_stabSub_commV hALt
    rwa [d321b_commV_conjAutSub, ← hU'] at h
  have hAC : A ≤ stabSub (fixV Mp) := d321d_le_stabSub_fixV (hA.le.trans hTn)
  have hAZ : A ≤ stabSub (commV L ⊓ fixV Mp) := d321d_stabSub_inf hAU hAC
  have hAZ' : A ≤ stabSub (U' ⊓ fixV Mp) := d321d_stabSub_inf hAU' hAC
  have hcount := d321d_split_count hexp hsplit.1.symm hsplit.2 hAU hAU' hAC
  have hrA : 0 < rk ↥A := hA.elem.rk_pos hA.ne
  have hrat : rkIdx (fixV A) ≤ 2 * rk ↥A := by
    have h := hA.rat
    unfold rAV at h
    have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA
    rw [div_le_iff₀ hpos] at h
    exact_mod_cast h
  have hA3 : commSeries A 3 = ⊥ := commSeries_eq_bot_of_le (by norm_num) hA.quad
  obtain ⟨B₂, hB₂⟩ : ∃ B₂ : Subgroup (MulAut W),
      B₂ = A ⊓ centSec (commV L) (commV L ⊓ fixV Mp) := ⟨_, rfl⟩
  have hB₂A : B₂ ≤ A := hB₂ ▸ inf_le_left
  have hB₂c : B₂ ≤ centSec (commV L) (commV L ⊓ fixV Mp) := hB₂ ▸ inf_le_right
  by_cases hc : ¬ A ≤ centSec (commV L) (commV L ⊓ fixV Mp) ∧
      rkIdx (fixV (autSec A (commV L) (commV L ⊓ fixV Mp))) + 2 * rk ↥B₂ ≤ 2 * rk ↥A
  · exact d321d_final (E := A) ⟨le_inf hAM hAL, hA.ne, hA.elem⟩ hA3 hAU hAZ hc.1
      (by rw [← hB₂]; exact hc.2)
  ·
    have hy : rkIdx (fixV (autSec A U' (U' ⊓ fixV Mp))) ≤ 2 * rk ↥B₂ ∧ 1 ≤ rk ↥B₂ := by
      by_cases hAc : A ≤ centSec (commV L) (commV L ⊓ fixV Mp)
      · have hB : B₂ = A := by rw [hB₂]; exact inf_eq_left.2 hAc
        rw [hB]
        omega
      · have hx : 2 * rk ↥A < rkIdx (fixV (autSec A (commV L) (commV L ⊓ fixV Mp))) +
            2 * rk ↥B₂ := by
          by_contra hle
          exact hc ⟨hAc, by omega⟩
        omega
    obtain ⟨hyle, hb1⟩ := hy
    have hbotA : A ⊓ centSec ⊤ (fixV Mp) = ⊥ :=
      d321d_faithful_top hL38 hstd htT htL hMp htriv hA.le hA.faithMp
    have hf' : B₂ ⊓ centSec U' (U' ⊓ fixV Mp) = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      rw [Subgroup.mem_bot]
      have hbA : b ∈ A := hB₂A hb.1
      have hbtop := d321d_centSec_top hsplit.1.symm (hAC hbA) (hB₂c hb.1) hb.2
      have h1 : b ∈ A ⊓ centSec ⊤ (fixV Mp) := ⟨hbA, hbtop⟩
      rw [hbotA, Subgroup.mem_bot] at h1
      exact h1
    obtain ⟨E, hE⟩ : ∃ E : Subgroup (MulAut W), E = conjAutSub t⁻¹ B₂ := ⟨_, rfl⟩
    have hmemE : ∀ e, e ∈ E ↔ t * e * t⁻¹ ∈ B₂ := fun e => by
      rw [hE, mem_conjAutSub_iff, inv_inv]
    have hEdef : ∀ e ∈ E, ∃ b ∈ B₂, e = t⁻¹ * b * t := fun e he =>
      ⟨t * e * t⁻¹, (hmemE e).1 he, by group⟩
    have hEM : E ≤ M := by
      intro e he
      obtain ⟨b, hb, rfl⟩ := hEdef e he
      exact M.mul_mem (M.mul_mem (M.inv_mem htM) (hAM (hB₂A hb))) htM
    have hEN : E ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
      intro e he
      obtain ⟨b, hb, rfl⟩ := hEdef e he
      have hbN : conjAutSub b (conjAutSub t L) = conjAutSub t L :=
        d321a_mem_normalizer_iff.mp (hALt (hB₂A hb))
      rw [d321a_mem_normalizer_iff, d321a_conjAutSub_mul, d321a_conjAutSub_mul, hbN,
        conjAutSub_inv_conjAutSub]
    have hrkE : rk ↥E = rk ↥B₂ := by rw [hE]; exact d321d_rk_conj _ _
    have hEne : E ≠ ⊥ := by
      intro h0
      rw [h0, rk_bot] at hrkE
      omega
    have hEel : IsElemAbelian2 E := by
      rw [hE]
      exact d321d_isElemAbelian2_conj _ (d321d_isElemAbelian2_mono hA.elem hB₂A)
    have hE3 : commSeries E 3 = ⊥ := by
      have h1 : commSeries B₂ 3 = ⊥ := le_bot_iff.1 ((commSeries_mono hB₂A 3).trans hA3.le)
      rw [hE]
      show commSeries (B₂.map (MulAut.conj t⁻¹).toMonoidHom) 3 = ⊥
      rw [Z391.commSeries_map_conj, h1, Subgroup.map_bot]
    have hEU : E ≤ stabSub (commV L) := d321d_le_stabSub_commV hEN
    have hEC : E ≤ stabSub (fixV Mp) := d321d_le_stabSub_fixV (hEM.trans hD.Mp_normal)
    have hEZ : E ≤ stabSub (commV L ⊓ fixV Mp) := d321d_stabSub_inf hEU hEC
    have hfixt : (fixV Mp).map t.toMonoidHom = fixV Mp := d321d_map_fixV (hTn htT)
    have hfE : E ⊓ centSec (commV L) (commV L ⊓ fixV Mp) = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      rw [Subgroup.mem_bot]
      have hb : t * e * t⁻¹ ∈ B₂ := (hmemE e).1 he.1
      have hc' := d321d_mem_centSec_conj (g := t) he.2
      rw [Subgroup.map_inf _ _ _ t.injective, hfixt, ← hU'] at hc'
      have h1 : t * e * t⁻¹ ∈ B₂ ⊓ centSec U' (U' ⊓ fixV Mp) := ⟨hb, hc'⟩
      rw [hf', Subgroup.mem_bot] at h1
      have h2 : e = t⁻¹ * (t * e * t⁻¹) * t := by group
      rw [h2, h1]
      group
    have hconj := d321d_rkIdx_fixV_autSec_conj t⁻¹ (E := B₂) (N := U') (D := U' ⊓ fixV Mp)
      inf_le_left (hB₂A.trans hAU') (hB₂A.trans hAZ')
    have hfixt' : (fixV Mp).map t⁻¹.toMonoidHom = fixV Mp :=
      d321b_fixV_map_inv hL38 hstd htT htL hMp
    have hU'' : U'.map t⁻¹.toMonoidHom = commV L := by rw [hU', d321b_map_map_inv]
    rw [Subgroup.map_inf _ _ _ t⁻¹.injective, hfixt', hU'', ← hE] at hconj
    have hmono := d321d_rkIdx_fixV_autSec_mono hB₂A (inf_le_left : U' ⊓ fixV Mp ≤ U') hAU' hAZ'
    refine d321d_final (E := E) ⟨le_inf hEM hEN, hEne, hEel⟩ hE3 hEU hEZ
      (fun h => hEne (by rw [← hfE]; exact (inf_eq_left.2 h).symm)) ?_
    rw [hfE, rk_bot]
    omega

theorem d321_qhat_restrict (hL38 : D3L38) (hstd : D3Std M Mp T L V)
    (htT : t ∈ T) (htL : t ∉ Subgroup.normalizer (L : Set (MulAut W)))
    (hMp : Mp = L ⊔ conjAutSub t L) {A : Subgroup (MulAut W)} (hA : QOff Mp T A (orbSup T V))
    (htriv : ∀ v ∈ V, ∀ g ∈ conjAutSub t L, g v = v) :
    qhatOf (autSec (M ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commV L)
      (commV L ⊓ fixV Mp)) ≤ ((2 : ℚ) : WithTop ℚ) := by
  by_cases hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))
  · exact d321d_case_normalizer hL38 hstd htT htL hMp hA htriv hAL
  · exact d321d_case_swap hL38 hstd htT htL hMp hA htriv hAL

end Cases

end CFSG.Quasithin
