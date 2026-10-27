module

public import CFSG.Quasithin.Vol2.Ch5ModulesFFA5
public import CFSG.Quasithin.EmptyFaithful.T1515dC
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113FourA7
public import Certificates.Data.A5

public section

namespace CFSG.Quasithin.H13.S5Pos

open Equiv Equiv.Perm

@[expose] def q0a : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3

@[expose] def q0b : Perm (Fin 5) := swap 0 2

@[expose] def q0L : List (Perm (Fin 5)) :=
  [1, q0a, q0a * q0a, q0a * q0a * q0a, q0b, q0b * q0a, q0b * q0a * q0a, q0b * q0a * q0a * q0a]

@[expose] def v0L : List (Perm (Fin 5)) :=
  [1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2]

theorem q0L_check :
    (q0L.all fun a => q0L.all fun b => q0L.contains (a * b)) &&
    q0L.all (fun a => decide (a * a * a * a = 1)) && decide q0L.Nodup &&
    q0L.all (fun a => decide (sign a = 1 ↔ a ∈ v0L)) &&
    (v0L.all fun a => v0L.all fun b => v0L.contains (a * b)) &&
    v0L.all (fun a => decide (a * a = 1)) && decide v0L.Nodup &&
    v0L.all (fun a => q0L.contains a) = true := by
  decide +kernel

theorem q0L_mul {a b : Perm (Fin 5)} (ha : a ∈ q0L) (hb : b ∈ q0L) : a * b ∈ q0L := by
  have h := q0L_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.1.1.1.1.1.1 a ha b hb

theorem q0L_pow {a : Perm (Fin 5)} (ha : a ∈ q0L) : a * a * a * a = 1 := by
  have h := q0L_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.2 a ha

theorem q0L_nodup : q0L.Nodup := by
  have h := q0L_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.2

theorem q0L_sign {a : Perm (Fin 5)} (ha : a ∈ q0L) : sign a = 1 ↔ a ∈ v0L := by
  have h := q0L_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.2 a ha

theorem v0L_mul {a b : Perm (Fin 5)} (ha : a ∈ v0L) (hb : b ∈ v0L) : a * b ∈ v0L := by
  have h := q0L_check
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact h.1.1.1.2 a ha b hb

theorem v0L_sq {a : Perm (Fin 5)} (ha : a ∈ v0L) : a * a = 1 := by
  have h := q0L_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2 a ha

theorem v0L_nodup : v0L.Nodup := by
  have h := q0L_check
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

@[expose] def q0 : Subgroup (Perm (Fin 5)) where
  carrier := {g | g ∈ q0L}
  mul_mem' ha hb := q0L_mul ha hb
  one_mem' := List.mem_cons_self
  inv_mem' {a} ha := by
    have hinv : a⁻¹ = a * a * a :=
      inv_eq_of_mul_eq_one_right (by simpa only [mul_assoc] using q0L_pow ha)
    change a⁻¹ ∈ q0L
    rw [hinv]
    exact q0L_mul (q0L_mul ha ha) ha

theorem mem_q0 {g : Perm (Fin 5)} : g ∈ q0 ↔ g ∈ q0L := Iff.rfl

@[expose] def v0 : Subgroup (Perm (Fin 5)) where
  carrier := {g | g ∈ v0L}
  mul_mem' ha hb := v0L_mul ha hb
  one_mem' := List.mem_cons_self
  inv_mem' {a} ha := by
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (v0L_sq ha)
    change a⁻¹ ∈ v0L
    rw [hinv]
    exact ha

theorem mem_v0 {g : Perm (Fin 5)} : g ∈ v0 ↔ g ∈ v0L := Iff.rfl

theorem card_eq_length {H : Subgroup (Perm (Fin 5))} {l : List (Perm (Fin 5))}
    (hH : ∀ g, g ∈ H ↔ g ∈ l) (hl : l.Nodup) : Nat.card H = l.length := by
  have h2 : (H : Set (Perm (Fin 5))) =
      ((l.toFinset : Finset (Perm (Fin 5))) : Set (Perm (Fin 5))) := by
    ext σ
    simp [hH]
  rw [← SetLike.coe_sort_coe, h2, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hl]

theorem card_q0 : Nat.card q0 = 8 := (card_eq_length (fun _ => mem_q0) q0L_nodup).trans rfl

theorem card_v0 : Nat.card v0 = 4 := (card_eq_length (fun _ => mem_v0) v0L_nodup).trans rfl

theorem card_dvd_eight {P : Subgroup (Perm (Fin 5))} (hP : IsPGroup 2 P) : Nat.card P ∣ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hd : Nat.card P ∣ 120 := by
    have h := Subgroup.card_subgroup_dvd_card P
    rw [Nat.card_perm, Nat.card_fin] at h
    exact (show Nat.factorial 5 = 120 by decide) ▸ h
  rw [hk] at hd ⊢
  have hk3 : k ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ 120 := (pow_dvd_pow 2 (by omega)).trans hd
    norm_num at h16
  exact (pow_dvd_pow 2 hk3).trans (by norm_num)

theorem exists_conj_eq_q0 {S : Subgroup (Perm (Fin 5))} (hS : IsPGroup 2 S)
    (h8 : Nat.card S = 8) : ∃ g : Perm (Fin 5), S.map (MulAut.conj g).toMonoidHom = q0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hSP⟩ := hS.exists_le_sylow
  have hPS : (P : Subgroup (Perm (Fin 5))) = S :=
    (Subgroup.eq_of_le_of_card_ge hSP (by
      rw [h8]
      exact Nat.le_of_dvd (by norm_num) (card_dvd_eight P.isPGroup'))).symm
  have hq2 : IsPGroup 2 q0 := IsPGroup.of_card (n := 3) (by rw [card_q0]; norm_num)
  obtain ⟨P', hP'⟩ := hq2.exists_le_sylow
  have hP'eq : (P' : Subgroup (Perm (Fin 5))) = q0 :=
    (Subgroup.eq_of_le_of_card_ge hP' (by
      rw [card_q0]
      exact Nat.le_of_dvd (by norm_num) (card_dvd_eight P'.isPGroup'))).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) P P'
  refine ⟨g, ?_⟩
  rw [← hPS, ← hP'eq, ← hg, Sylow.coe_subgroup_smul]
  rfl

@[expose] def c5 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def c3 : Perm (Fin 5) := swap 0 1 * swap 1 2

theorem c5_mem : c5 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem c3_mem : c3 ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem card_d5Fix_c5c3 : (d5Fix {c5, c3}).card ≤ 1 := by
  decide +kernel

theorem conj_not_mem_q0L :
    ∀ δ : Perm (Fin 5), δ * δ * δ = 1 → δ ≠ 1 → (∀ v ∈ v0L, δ * v * δ⁻¹ ∈ v0L) →
      ∀ b ∈ q0L, sign b ≠ 1 → δ * b * δ⁻¹ ∉ q0L := by
  decide +kernel

end CFSG.Quasithin.H13.S5Pos

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm
open scoped IsMulCommutative

section S5Side

variable {G : Type} [Group G] [Finite G]

theorem not_le_normalizer_thompsonJ_of_s5 {T L W D : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLs : IsSimpleGroup (O2Q L)) (hT2 : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLsyl : IsSylowTwoOf (T ⊓ L) L)
    (hWe : IsElemAbelian 2 W) (hWT : W ≤ T) (hS5 : IsS5ModCh5 L T W)
    (hJW : ¬ thompsonJ T ≤ Subgroup.centralizer (W : Set G))
    (hDL : D ≤ L) (hDN : D ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G))
    (hD3 : Nat.card D = 3) :
    ¬ D ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
  intro hDJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA5 := isA5ModuleUnder_of_isS5ModCh5 hS5 hL hT2 hTL
  have hcommW := IsA5ModuleUnder.commutator_eq hA5
  obtain ⟨-, hc', π', hπ'⟩ := hA5
  obtain ⟨hN, hc, π, hπ⟩ := hS5
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := le_sup_left.trans hN
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := le_sup_right.trans hN
  have hπi : Function.Injective π :=
    G64.RealizesVia.injective_of_faithful' (G64.symDn_faithful (by norm_num)) hπ
  have hπs : Function.Surjective π := hπ.1
  have hKX : (autOn L W) ≤ (autOn (L ⊔ T) W) := A4.autOn_mono le_sup_left
  have hK0 : (autOn L W) ≠ ⊥ := by
    intro hb
    have hX : autOn (L ⊔ T) W = autOn T W := by
      rw [autOn_sup_eq_sup hLW hTW, hb, bot_sup_eq]
    have h2 : IsPGroup 2 ↥(autOn (L ⊔ T) W) := by
      rw [hX]
      exact autOn_isPGroup hT2
    exact not_isPGroup_of_symDn hπ h2
  have hKeq := eq_map_alternatingGroup hπs hKX (autOn_sup_le_normalizer_autOn hTL)
    (autOn_perfect hL hLW) hK0
  have hcomm : commV (autOn L W) = ⊤ := by
    rw [commV_autOn_eq1527d hLW, hcommW, Subgroup.subgroupOf_self]
  have hfix : fixV (autOn L W) = ⊥ := by
    rw [← Subgroup.card_le_one_iff_eq_bot]
    refine (card_le_d5Fix hπ' le_top {S5Pos.c5, S5Pos.c3} ?_ ?_).trans S5Pos.card_d5Fix_c5c3
    · intro γ hγ
      rw [Finset.mem_insert, Finset.mem_singleton] at hγ
      rcases hγ with rfl | rfl
      · exact S5Pos.c5_mem
      · exact S5Pos.c3_mem
    · intro γ _ w hw
      exact hw _ (π' γ).2
  have hDir : IsIntDirect (commV (autOn L W)) (fixV (autOn L W)) ⊤ :=
    ⟨by rw [hcomm, top_sup_eq], by rw [hfix, inf_bot_eq]⟩
  have hR : AlternatingNatural (autOn L W) (commV (autOn L W)) ⊥ 5 := by
    rw [hcomm]
    exact ⟨π', hπ'⟩
  obtain ⟨A, hA, hAW⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set G) := by
    by_contra hall
    push Not at hall
    exact hJW (iSup₂_le fun A hA => hall A hA)
  have hff := (offender_core hWe hWT hTW hA (B := ⊥) bot_le).1
  rw [B1.card_bot_mul_card_fixV] at hff
  have hA2 := isA2_autI hWe hTW hA.1 hA.2.1 hAW
  have hAK : ¬ autOn A W ≤ (autOn L W) := by
    intro hAK
    have h1 := card_mul_card_fixV_lt_of_altDn_five hDir hR hAK hA2.2.1 hA2.2.2
    exact absurd hff (not_le.mpr h1)
  obtain ⟨φ, hφA, hφK⟩ := Set.not_subset.mp hAK
  obtain ⟨⟨a, haA⟩, haφ⟩ := (A4.mem_autOn_iff (hA.1.trans hTW)).mp hφA
  have haT : a ∈ T := hA.1 haA
  have haJ : a ∈ thompsonJ T := B6.le_thompsonJ hA haA
  have hDne : D ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hD3
    omega
  obtain ⟨⟨d, hdD⟩, hd1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDne
  have hd1' : d ≠ 1 := fun h1 => hd1 (Subtype.ext h1)
  have hd3 : d ^ 3 = 1 := by
    have h1 := orderOf_dvd_natCard (⟨d, hdD⟩ : ↥D)
    rw [hD3, Subgroup.orderOf_mk] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hdL : d ∈ L := hDL hdD
  have hCL : L ⊓ Subgroup.centralizer (W : Set G) ≤ pCoreOf 2 L := by
    refine le_pCoreOf_of_normal_of_ne hL hLs inf_le_left (fun y hy =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hy, B6.le_normalizer_centralizer hLW hy⟩) fun he => hK0 ?_
    exact (autI_eq_bot_iff hWe hLW).mpr (he ▸ inf_le_right)
  have hdW : d ∉ Subgroup.centralizer (W : Set G) := by
    intro hdc
    have h1 : d ∈ pCoreOf 2 L := hCL ⟨hdL, hdc⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨d, h1⟩
    have e1 : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hord : orderOf d ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one e1) (orderOf_dvd_of_pow_eq_one hd3)
    rw [show Nat.gcd (2 ^ k) 3 = 1 from Nat.Coprime.pow_left k (by norm_num), Nat.dvd_one,
      orderOf_eq_one_iff] at hord
    exact hd1' hord
  have hmemX : ∀ y : ↥(L ⊔ T), A4.actionOn W (L ⊔ T) hN y ∈ (autOn (L ⊔ T) W) :=
    fun y => (A4.mem_autOn_iff hN).mpr ⟨y, rfl⟩
  set ψ₀ : ↥(L ⊔ T) →* ↥(autOn (L ⊔ T) W) :=
    (A4.actionOn W (L ⊔ T) hN).codRestrict (autOn (L ⊔ T) W) hmemX with hψ₀
  set σ : ↥(autOn (L ⊔ T) W) ≃* Perm (Fin 5) := (MulEquiv.ofBijective π ⟨hπi, hπs⟩).symm with hσ
  set ψ : ↥(L ⊔ T) →* Perm (Fin 5) := σ.toMonoidHom.comp ψ₀ with hψ
  have hπψ : ∀ y, π (ψ y) = ψ₀ y := fun y => by
    rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hσ]
    exact MulEquiv.ofBijective_apply_symm_apply _ _
  have hψπ : ∀ y τ, ψ₀ y = π τ → ψ y = τ := fun y τ h => by
    apply hπi
    rw [hπψ, h]
  have hψL : ∀ y : ↥(L ⊔ T), (y : G) ∈ L → ψ y ∈ alternatingGroup (Fin 5) := by
    intro y hy
    have h1 : ((ψ₀ y : ↥(autOn (L ⊔ T) W)) : MulAut ↥W) ∈ autOn L W :=
      (A4.mem_autOn_iff hLW).mpr ⟨⟨y, hy⟩, rfl⟩
    rw [hKeq] at h1
    obtain ⟨τ, hτ, hτe⟩ := h1
    rw [hψπ y τ (Subtype.ext hτe.symm)]
    exact hτ
  have hψK : ∀ y : ↥(L ⊔ T), ψ y ∈ alternatingGroup (Fin 5) →
      ((ψ₀ y : ↥(autOn (L ⊔ T) W)) : MulAut ↥W) ∈ autOn L W := by
    intro y hy
    rw [hKeq, ← hπψ y]
    exact ⟨ψ y, hy, rfl⟩
  have hψsurj : ∀ τ ∈ alternatingGroup (Fin 5), ∃ y : ↥(L ⊔ T), (y : G) ∈ L ∧ ψ y = τ := by
    intro τ hτ
    have h1 : ((π τ : ↥(autOn (L ⊔ T) W)) : MulAut ↥W) ∈ autOn L W := by
      rw [hKeq]
      exact ⟨τ, hτ, rfl⟩
    obtain ⟨l, hl⟩ := (A4.mem_autOn_iff hLW).mp h1
    refine ⟨⟨l, Subgroup.mem_sup_left l.2⟩, l.2, hψπ _ τ (Subtype.ext ?_)⟩
    exact hl
  have hψ1 : ∀ y : ↥(L ⊔ T), ψ y = 1 → (y : G) ∈ Subgroup.centralizer (W : Set G) := by
    intro y hy
    have h1 : ψ₀ y = 1 := by
      rw [← hπψ y, hy]
      exact π.map_one
    exact (A4.actionOn_eq_one_iff hN y).mp (congrArg Subtype.val h1)
  set ya : ↥(L ⊔ T) := ⟨a, Subgroup.mem_sup_right haT⟩ with hya
  set yd : ↥(L ⊔ T) := ⟨d, Subgroup.mem_sup_left hdL⟩ with hyd
  have hb : Perm.sign (ψ ya) ≠ 1 := by
    intro h1
    apply hφK
    rw [← haφ]
    exact hψK ya (Equiv.Perm.mem_alternatingGroup.mpr h1)
  have hδ1 : ψ yd ≠ 1 := fun h1 => hdW (hψ1 yd h1)
  have hδ3 : ψ yd * ψ yd * ψ yd = 1 := by
    rw [← map_mul, ← map_mul]
    have : yd * yd * yd = 1 := Subtype.ext (by simpa [pow_succ, mul_assoc] using hd3)
    rw [this, map_one]
  set Tb := (T.subgroupOf (L ⊔ T)).map ψ with hTb
  set Sb := ((T ⊓ L).subgroupOf (L ⊔ T)).map ψ with hSb
  have hTb2 : IsPGroup 2 ↥Tb :=
    (hT2.comap_of_injective _ (Subgroup.subtype_injective _)).map _
  have hSbT : Sb ≤ Tb := Subgroup.map_mono (Subgroup.subgroupOf_mono _ inf_le_left)
  have hSbA : Sb ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hψL y (Subgroup.mem_subgroupOf.mp hy).2
  have hbT : ψ ya ∈ Tb := ⟨ya, Subgroup.mem_subgroupOf.mpr haT, rfl⟩
  have hdT : ∀ s ∈ Sb, ψ yd * s * (ψ yd)⁻¹ ∈ Sb := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hy
    refine ⟨yd * y * yd⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    show yd * y * yd⁻¹ ∈ (T ⊓ L).subgroupOf (L ⊔ T)
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp (hDN hdD) _).mp hy'
  have hSb4 : Nat.card Sb = 4 := by
    set f : ↥L →* Perm (Fin 5) := ψ.comp (Subgroup.inclusion le_sup_left) with hf
    have hfr : f.range = alternatingGroup (Fin 5) := by
      apply le_antisymm
      · rintro _ ⟨l, rfl⟩
        exact hψL _ l.2
      · intro τ hτ
        obtain ⟨y, hyL, hy⟩ := hψsurj τ hτ
        exact ⟨⟨y, hyL⟩, hy⟩
    set H := (T ⊓ L).subgroupOf L with hH
    have hsub : (T ⊓ L).subgroupOf (L ⊔ T) = H.map (Subgroup.inclusion le_sup_left) := by
      refine Subgroup.ext fun y => ⟨fun hy => ?_, ?_⟩
      · have hy' : (y : G) ∈ T ⊓ L := Subgroup.mem_subgroupOf.mp hy
        exact ⟨⟨y, hy'.2⟩, Subgroup.mem_subgroupOf.mpr hy', rfl⟩
      · rintro ⟨l, hl, rfl⟩
        exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hl)
    have hSbf : Sb = H.map f := by
      rw [hSb, hsub, Subgroup.map_map]
    set f' : ↥L →* ↥f.range := f.rangeRestrict with hf'
    have hidx : (H.map f').index ∣ H.index :=
      Subgroup.index_map_dvd _ f.rangeRestrict_surjective
    have hodd : ¬ 2 ∣ (H.map f').index := fun h2 => hLsyl.2.2 (h2.trans hidx)
    have hc1 : Nat.card ↥(H.map f') = Nat.card Sb := by
      rw [hSbf]
      have h1 : (H.map f').map f.range.subtype = H.map f := by
        rw [Subgroup.map_map]
        rfl
      rw [← h1]
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv
    have h60 : Nat.card ↥f.range = 60 := by
      rw [hfr, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hmul := Subgroup.card_mul_index (H.map f')
    rw [hc1, h60] at hmul
    have h4 : 4 ∣ Nat.card Sb := by
      have hcop : Nat.Coprime 4 (H.map f').index :=
        Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega)))
      exact hcop.dvd_of_dvd_mul_right (by rw [hmul]; norm_num)
    have hSb2 : IsPGroup 2 ↥Sb := hTb2.to_le hSbT
    have hd60 : Nat.card Sb ∣ 60 := by
      rw [← hmul]
      exact dvd_mul_right _ _
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSb2
    rw [hk] at h4 hd60 ⊢
    have hk2 : k ≤ 2 := by
      by_contra hk3
      have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
      have := h8.trans hd60
      norm_num at this
    have hk2' : 2 ≤ k := by
      by_contra hk1
      have hk1' : k ≤ 1 := by omega
      have := Nat.le_of_dvd (pow_pos (by norm_num) k) h4
      have : 2 ^ k ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hk1'
      omega
    rw [show k = 2 by omega]
    norm_num
  have hTb8 : Nat.card Tb = 8 := by
    have hd8 := S5Pos.card_dvd_eight hTb2
    set Tb0 := Tb ⊓ alternatingGroup (Fin 5) with hTb0
    have hle : Sb ≤ Tb0 := le_inf hSbT hSbA
    have h4 : 4 ≤ Nat.card Tb0 := hSb4 ▸ Subgroup.card_le_of_le hle
    have hlt : Tb0 < Tb := by
      refine lt_of_le_of_ne inf_le_left fun he => hb ?_
      have : ψ ya ∈ Tb0 := he ▸ hbT
      exact Equiv.Perm.mem_alternatingGroup.mp this.2
    have hdvd : Nat.card Tb0 ∣ Nat.card Tb := Subgroup.card_dvd_of_le inf_le_left
    have hne : Nat.card Tb0 ≠ Nat.card Tb := fun he =>
      hlt.ne (Subgroup.eq_of_le_of_card_ge inf_le_left he.ge)
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : 2 ≤ c := by
      rcases Nat.lt_or_ge c 2 with hc1 | hc1
      · interval_cases c
        · rw [mul_zero] at hc
          exact absurd hc (Nat.card_pos.ne')
        · rw [mul_one] at hc
          exact absurd hc.symm hne
      · exact hc1
    have h8 : 8 ≤ Nat.card Tb := by rw [hc]; nlinarith
    exact Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hd8) h8
  obtain ⟨g, hg⟩ := S5Pos.exists_conj_eq_q0 hTb2 hTb8
  have hgT : ∀ x ∈ Tb, g * x * g⁻¹ ∈ S5Pos.q0L := fun x hx => by
    rw [← S5Pos.mem_q0, ← hg]
    exact ⟨x, hx, rfl⟩
  set Sg := Sb.map (MulAut.conj g).toMonoidHom with hSg
  have hSgV : Sg ≤ S5Pos.v0 := by
    rintro _ ⟨s, hs, rfl⟩
    show g * s * g⁻¹ ∈ S5Pos.v0L
    rw [← S5Pos.q0L_sign (hgT s (hSbT hs))]
    rw [map_mul, map_mul, map_inv, Equiv.Perm.mem_alternatingGroup.mp (hSbA hs), mul_one,
      mul_inv_cancel]
  have hSg4 : Nat.card Sg = 4 := by
    rw [hSg, Subgroup.card_map_of_injective (MulAut.conj g).injective, hSb4]
  have hSgeq : Sg = S5Pos.v0 :=
    Subgroup.eq_of_le_of_card_ge hSgV (by rw [hSg4, S5Pos.card_v0])
  have hδV : ∀ v ∈ S5Pos.v0L, (g * ψ yd * g⁻¹) * v * (g * ψ yd * g⁻¹)⁻¹ ∈ S5Pos.v0L := by
    intro v hv
    have hv' : v ∈ Sg := hSgeq ▸ S5Pos.mem_v0.mpr hv
    obtain ⟨s, hs, rfl⟩ := hv'
    rw [← S5Pos.mem_v0, ← hSgeq]
    refine ⟨ψ yd * s * (ψ yd)⁻¹, hdT s hs, ?_⟩
    show g * (ψ yd * s * (ψ yd)⁻¹) * g⁻¹ = _
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hδ3' : (g * ψ yd * g⁻¹) * (g * ψ yd * g⁻¹) * (g * ψ yd * g⁻¹) = 1 := by
    calc (g * ψ yd * g⁻¹) * (g * ψ yd * g⁻¹) * (g * ψ yd * g⁻¹) =
        g * (ψ yd * ψ yd * ψ yd) * g⁻¹ := by group
      _ = 1 := by rw [hδ3]; group
  have hδ1' : g * ψ yd * g⁻¹ ≠ 1 := by
    intro h1
    apply hδ1
    calc ψ yd = g⁻¹ * (g * ψ yd * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hb' : g * ψ ya * g⁻¹ ∈ S5Pos.q0L := hgT _ hbT
  have hbs : Perm.sign (g * ψ ya * g⁻¹) ≠ 1 := by
    rw [map_mul, map_mul, map_inv, mul_comm (Perm.sign g), mul_assoc, mul_inv_cancel, mul_one]
    exact hb
  have hnot := S5Pos.conj_not_mem_q0L _ hδ3' hδ1' hδV _ hb' hbs
  apply hnot
  have hdad : d * a * d⁻¹ ∈ T :=
    B6.thompsonJ_le T ((Subgroup.mem_normalizer_iff.mp (hDJ hdD) a).mp haJ)
  have h1 : ψ (yd * ya * yd⁻¹) ∈ Tb := ⟨yd * ya * yd⁻¹, Subgroup.mem_subgroupOf.mpr hdad, rfl⟩
  rw [map_mul, map_mul, map_inv] at h1
  have h2 := hgT _ h1
  have e : (g * ψ yd * g⁻¹) * (g * ψ ya * g⁻¹) * (g * ψ yd * g⁻¹)⁻¹ =
      g * (ψ yd * ψ ya * (ψ yd)⁻¹) * g⁻¹ := by group
  rw [e]
  exact h2

end S5Side

end CFSG.Quasithin.H13
