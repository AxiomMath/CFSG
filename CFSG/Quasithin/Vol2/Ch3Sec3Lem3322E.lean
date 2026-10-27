module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3322D

public section

namespace CFSG.Quasithin.H13.L3322

open Equiv Equiv.Perm
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique hiding evenWeight
open CFSG.Quasithin.H13.A7 (IsCoordAct vec natLam)
open CFSG.Quasithin.SteinbergCB (permAct7 evenWeight sevenP permAct7_conj permAct7_inv_apply)
open scoped IsMulCommutative

section Abstract

theorem not_isSolvable_of_simple {A : Type*} [Group A] (hs : IsSimpleGroup A) {a b : A}
    (hab : a * b ≠ b * a) : ¬ Group.IsSolvable A := by
  intro hsol
  rw [← IsSimpleGroup.comm_iff_isSolvable] at hsol
  exact hab (hsol a b)

theorem card_range_dvd_of_isSolvable {Y A B : Type*} [Group Y] [Finite Y] [Group A] [Group B]
    (α : Y →* A) (β : Y →* B) (hαs : IsSimpleGroup α.range)
    (hαn : ¬ Group.IsSolvable α.range) (hβk : Group.IsSolvable β.ker) :
    Nat.card α.range ∣ Nat.card β.range := by
  have hle : β.ker ≤ α.ker := by
    have hN : (β.ker.map α.rangeRestrict).Normal :=
      β.normal_ker.map α.rangeRestrict α.rangeRestrict_surjective
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hαs _ hN with h | h
    · intro x hx
      have h1 : α.rangeRestrict x ∈ β.ker.map α.rangeRestrict := Subgroup.mem_map_of_mem _ hx
      rw [h, Subgroup.mem_bot] at h1
      exact MonoidHom.mem_ker.2 (congrArg Subtype.val h1)
    · exfalso
      apply hαn
      have hsurj : Function.Surjective (α.rangeRestrict.comp β.ker.subtype) := by
        intro y
        have hy : y ∈ β.ker.map α.rangeRestrict := h ▸ Subgroup.mem_top y
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨⟨x, hx⟩, rfl⟩
      exact Group.isSolvable_of_surjective hsurj
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivRange β).toEquiv]
  exact Subgroup.index_dvd_of_le hle

theorem isSolvable_ker_comp {Y L S : Type*} [Group Y] [Group L] [Group S] (g : Y →* L)
    (hg : Function.Injective g) (f : L →* S) [Group.IsSolvable f.ker] :
    Group.IsSolvable (f.comp g).ker := by
  let k : (f.comp g).ker →* f.ker :=
    (g.comp (f.comp g).ker.subtype).codRestrict f.ker fun x => x.2
  exact Group.isSolvable_of_isSolvable_injective (f := k) fun x y hxy =>
    Subtype.ext (hg (congrArg Subtype.val hxy))

theorem le_normalizer_of_conj_mem {A : Type*} [Group A] {H S : Subgroup A}
    (h : ∀ s ∈ S, ∀ x ∈ H, s * x * s⁻¹ ∈ H) : S ≤ Subgroup.normalizer (H : Set A) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h s hs x, fun hx => ?_⟩
  have h1 := h s⁻¹ (S.inv_mem hs) _ hx
  rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at h1

theorem eq_top_of_sixty_dvd {A : Type*} [Group A] [Finite A] (hs : IsSimpleGroup A)
    (hA : Nat.card A = 360) {H S : Subgroup A} (h60 : 60 ∣ Nat.card H) (hS8 : Nat.card S = 8)
    (hSH : S ≤ Subgroup.normalizer (H : Set A)) : H = ⊤ := by
  classical
  set H' := H ⊔ S with hH'
  have hl : Nat.lcm 60 8 ∣ Nat.card H' :=
    Nat.lcm_dvd (h60.trans (Subgroup.card_dvd_of_le le_sup_left))
      (hS8 ▸ Subgroup.card_dvd_of_le le_sup_right)
  have h120 : 120 ∣ Nat.card H' := by
    rwa [show Nat.lcm 60 8 = 120 by norm_num] at hl
  have hidx := H'.index_mul_card
  rw [hA] at hidx
  have hi3 : H'.index ≤ 3 := by
    have h1 : H'.index * 120 ∣ 3 * 120 := by
      rw [show 3 * 120 = 360 by norm_num, ← hidx]
      exact Nat.mul_dvd_mul_left _ h120
    exact Nat.le_of_dvd (by norm_num) (Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1)
  have htop : H' = ⊤ := by
    have hdvd := H'.index_normalCore_dvd_factorial_index
    rcases (Subgroup.normalCore_normal H').eq_bot_or_eq_top with hb | ht
    · exfalso
      rw [hb, Subgroup.index_bot, hA] at hdvd
      have h6 : H'.index.factorial ≤ 6 := (Nat.factorial_le hi3).trans (by decide)
      have := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
      omega
    · have hle := Subgroup.normalCore_le H'
      rw [ht, top_le_iff] at hle
      exact hle
  have hHn : H.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer hSH
  rcases hHn.eq_bot_or_eq_top with hb | ht
  · rw [hb, Subgroup.card_bot] at h60
    norm_num at h60
  · exact ht

theorem eq_of_sixty_dvd {Γ : Type*} [Group Γ] [Finite Γ] {A H S : Subgroup Γ}
    (hs : IsSimpleGroup A) (hA : Nat.card A = 360) (hHA : H ≤ A) (hSA : S ≤ A)
    (h60 : 60 ∣ Nat.card H) (hS8 : Nat.card S = 8) (hSH : ∀ s ∈ S, ∀ x ∈ H, s * x * s⁻¹ ∈ H) :
    H = A := by
  have h1 : H.subgroupOf A = ⊤ := by
    refine eq_top_of_sixty_dvd hs hA (S := S.subgroupOf A) ?_ ?_
      (le_normalizer_of_conj_mem fun s hs x hx => ?_)
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHA).toEquiv]
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSA).toEquiv]
    · rw [Subgroup.mem_subgroupOf] at hs hx ⊢
      exact hSH _ hs _ hx
  exact le_antisymm hHA (Subgroup.subgroupOf_eq_top.1 h1)

end Abstract

section Coord

variable {G : Type} [Group G]

theorem isCoordAct_conj {V : Subgroup G} (ψ : V ≃* Multiplicative (evenWeight 7)) {n m : G}
    (hn : n ∈ Subgroup.normalizer (V : Set G)) (hm : m ∈ Subgroup.normalizer (V : Set G))
    {σ τ : Perm (Fin 7)} (hσ : IsCoordAct ψ n σ) (hτ : IsCoordAct ψ m τ) :
    IsCoordAct ψ (n * m * n⁻¹) (σ * τ * σ⁻¹) := by
  intro x y hxy
  have hx1 : n⁻¹ * x * n ∈ V := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) x).1 x.2
    rwa [inv_inv] at h1
  set x1 : V := ⟨n⁻¹ * x * n, hx1⟩ with hx1def
  set y1 : V := ⟨m * x1 * m⁻¹, (Subgroup.mem_normalizer_iff.1 hm x1).1 x1.2⟩ with hy1def
  have hx : (x : G) = n * x1 * n⁻¹ := by
    change (x : G) = n * (n⁻¹ * x * n) * n⁻¹
    group
  have hy : (y : G) = n * y1 * n⁻¹ := by
    rw [hxy]
    change n * m * n⁻¹ * x * (n * m * n⁻¹)⁻¹ = n * (m * (n⁻¹ * x * n) * m⁻¹) * n⁻¹
    group
  rw [hσ y1 y hy, hτ x1 y1 rfl, hσ x1 x hx, permAct7_conj, permAct7_inv_apply]

end Coord

section Final

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}
  {ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)}

theorem not_isSolvable_altFive : ¬ Group.IsSolvable A7.altFive := by
  refine not_isSolvable_of_simple A7.isSimpleGroup_altFive
    (a := ⟨⟨L3317.cyc012, L3317.cyc012_mem⟩, L3317.cyc012_mem_altFive⟩)
    (b := ⟨⟨L3317.cyc01234, L3317.cyc01234_mem⟩, L3317.cyc01234_mem_altFive⟩) fun h1 => ?_
  have h2 := congrArg (fun x : A7.altFive => ((x : alternatingGroup (Fin 7)) : Perm (Fin 7))) h1
  exact absurd h2 (by decide)

theorem not_isSolvable_stabA7_vecSix : ¬ Group.IsSolvable (A7.stabA7 A7.vecSix) := by
  obtain ⟨a, b, hab⟩ := A7.stabA7_vecSix_nonabelian
  exact not_isSolvable_of_simple A7.isSimpleGroup_stabA7_vecSix hab

theorem nat_card_sevenP_comap :
    Nat.card (sevenP.comap (alternatingGroup (Fin 7)).subtype) = 8 := by
  rw [← A7.nat_card_sevenP_inf_alternating]
  exact Nat.card_congr ⟨fun s => ⟨s.1.1, s.2, s.1.2⟩, fun p => ⟨⟨p.1, p.2.2⟩, p.2.1⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem false_of_conj (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hc : Coord322 T L ψ) {a b : ↥⁅vPlus L T, L⁆} (ha : vec ψ a = vecZO)
    (hb : vec ψ b = A7.vecSix)
    (hθ : thetaOf (Subgroup.centralizer ({(b : G)} : Set G)) ≤ lTheta L b) {d : G}
    (hdT : d ∈ Subgroup.normalizer (T : Set G)) (hd : d * a * d⁻¹ = b) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLW := L3317.le_normalizer_commV h
  have hTW := L3317.T_le_normalizer_commV hTL
  have haZ : (a : G) ∈ quasithinOmegaOneCenter T := (mem_Z_iff h hTL hc a).2 (Or.inr (Or.inl ha))
  set τ : Perm (Fin 7) := swap 0 5 * swap 1 6 with hτ
  set ψ' := ψ.trans (A7.relabelE τ) with hψ'
  have ha' : vec ψ' a = A7.vecFS := by
    rw [hψ', A7.vec_trans_relabelE, ha]
    decide +kernel
  have hLact' : ∀ l ∈ L, ∃ σ ∈ alternatingGroup (Fin 7), IsCoordAct ψ' l σ := fun l hl => by
    obtain ⟨σ, hσ, hact⟩ := hc.Lact l hl
    exact ⟨τ * σ * τ⁻¹, (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ,
      (A7.isCoordAct_trans_relabelE_iff ψ τ).2 hact⟩
  have hLonto' : ∀ σ ∈ alternatingGroup (Fin 7), ∃ l ∈ L, IsCoordAct ψ' l σ := fun σ hσ => by
    have hσ' : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ alternatingGroup (Fin 7) :=
      (alternatingGroup.normal (α := Fin 7)).conj_mem σ hσ τ⁻¹
    rw [inv_inv] at hσ'
    obtain ⟨l, hl, hact⟩ := hc.Lonto _ hσ'
    exact ⟨l, hl, (A7.isCoordAct_trans_relabelE_iff' ψ τ).2 hact⟩
  set K := perfectCore (lTheta L (a : G)) with hK
  have hKL : K ≤ L := (perfectCore_le _).trans (lTheta_le L _)
  have hKa : K ≤ Subgroup.centralizer ({(a : G)} : Set G) :=
    (perfectCore_le _).trans (lTheta_le_centralizer L _)
  set lam' := natLam hLW hLact' with hlam'
  have hmap' : (K.subgroupOf L).map lam' = A7.altFive :=
    A7.natLam_map_Ke_two hLW hLact' hLonto' ha'
  have hcen' := mul_mem_pCore_of_natLam_eq_one hLW hLact' hLonto' h.Lq
  have hKθ : K ≤ thetaOf K := le_thetaOf_of_altFive_le hKL (perfectCore_perfect _) lam' hcen'
    (by rw [hmap']; exact A7.isSimpleGroup_altFive) hmap'.ge
  set f := (MulAut.conj d).toMonoidHom with hf
  set X := K.map f with hX
  have hXb : X ≤ Subgroup.centralizer ({(b : G)} : Set G) := by
    rw [← hd]
    exact (Subgroup.map_mono hKa).trans (map_conj_centralizer_le d a)
  have hXθ : X ≤ lTheta L b :=
    calc X ≤ (thetaOf K).map f := Subgroup.map_mono hKθ
      _ ≤ thetaOf X := map_thetaOf_le K f (MulAut.conj d).injective
      _ ≤ thetaOf (Subgroup.centralizer ({(b : G)} : Set G)) := A7.theta_mono hXb
      _ ≤ lTheta L b := hθ
  have hXL : X ≤ L := hXθ.trans (lTheta_le L _)
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    (T_le_normalizer_lTheta hTL haZ).trans (normalizer_le_normalizer_perfectCore _)
  have hTX : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X := by
    rintro t ht _ ⟨k, hk, rfl⟩
    have ht' : d⁻¹ * t * d ∈ T := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hdT) t).1 ht
      rwa [inv_inv] at h1
    have hk' : (d⁻¹ * t * d) * k * (d⁻¹ * t * d)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (hTK ht') k).1 hk
    refine ⟨_, hk', ?_⟩
    simp only [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  set ρ := natLam hLW hc.Lact with hρ
  set Hρ := (X.subgroupOf L).map ρ with hHρ
  have hHA : Hρ ≤ A7.stabA7 A7.vecSix := by
    rintro _ ⟨x, hx, rfl⟩
    rw [A7.mem_stabA7, ← hb]
    exact (A7.mem_centralizer_iff_natLam hLW hc.Lact b x).1 (hXb (Subgroup.mem_subgroupOf.1 hx))
  set S := sevenP.comap (alternatingGroup (Fin 7)).subtype with hS
  have hSA : S ≤ A7.stabA7 A7.vecSix := fun s hs => sevenP_fix_vecSix hs
  have hSH : ∀ s ∈ S, ∀ y ∈ Hρ, s * y * s⁻¹ ∈ Hρ := by
    rintro s hs _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hact⟩ := hc.Tonto s ⟨hs, s.2⟩
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.1 hx
    have htx : t * x * t⁻¹ ∈ L := hXL (hTX t ht x hxX)
    refine ⟨⟨t * x * t⁻¹, htx⟩, Subgroup.mem_subgroupOf.2 (hTX t ht x hxX), ?_⟩
    apply Subtype.ext
    rw [A7.natLam_eq hLW hc.Lact ⟨t * x * t⁻¹, htx⟩ (isCoordAct_conj ψ (hTW ht) (hLW x.2) hact
      (A7.natLam_spec hLW hc.Lact x))]
    rfl
  set α := lam'.comp (Subgroup.inclusion hKL) with hα
  have hαr : α.range = A7.altFive := (range_comp_inclusion hKL lam').trans hmap'
  let γ : ↥K →* ↥L := (f.comp K.subtype).codRestrict L fun k => hXL ⟨k, k.2, rfl⟩
  have hγ : Function.Injective γ := fun x y hxy =>
    Subtype.ext ((MulAut.conj d).injective (congrArg Subtype.val hxy))
  set β := ρ.comp γ with hβ
  have hβr : β.range = Hρ := by
    rw [MonoidHom.range_comp]
    congr 1
    ext l
    constructor
    · rintro ⟨k, rfl⟩
      exact Subgroup.mem_subgroupOf.2 ⟨k, k.2, rfl⟩
    · intro hl
      obtain ⟨k, hk, hkl⟩ := Subgroup.mem_subgroupOf.1 hl
      exact ⟨⟨k, hk⟩, Subtype.ext hkl⟩
  have : Group.IsSolvable ρ.ker :=
    isSolvable_ker_of_comm ρ (mul_mem_pCore_of_natLam_eq_one hLW hc.Lact hc.Lonto h.Lq)
  have : Group.IsSolvable lam'.ker := isSolvable_ker_of_comm lam' hcen'
  have hαk : Group.IsSolvable α.ker :=
    isSolvable_ker_comp (Subgroup.inclusion hKL) (Subgroup.inclusion_injective hKL) lam'
  have hβk : Group.IsSolvable β.ker := isSolvable_ker_comp γ hγ ρ
  have hdiv := card_range_dvd_of_isSolvable α β (by rw [hαr]; exact A7.isSimpleGroup_altFive)
    (by rw [hαr]; exact not_isSolvable_altFive) hβk
  rw [hαr, A7.nat_card_altFive, hβr] at hdiv
  have hHeq : Hρ = A7.stabA7 A7.vecSix :=
    eq_of_sixty_dvd A7.isSimpleGroup_stabA7_vecSix A7.nat_card_stabA7_vecSix hHA hSA hdiv
      nat_card_sevenP_comap hSH
  have hdiv' := card_range_dvd_of_isSolvable β α
    (by rw [hβr, hHeq]; exact A7.isSimpleGroup_stabA7_vecSix)
    (by rw [hβr, hHeq]; exact not_isSolvable_stabA7_vecSix) hαk
  rw [hβr, hHeq, A7.nat_card_stabA7_vecSix, hαr, A7.nat_card_altFive] at hdiv'
  norm_num at hdiv'

end Final

end CFSG.Quasithin.H13.L3322
