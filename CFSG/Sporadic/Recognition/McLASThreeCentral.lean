module

public import CFSG.Sporadic.Recognition.McLASClasses

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup Pointwise CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Blueprint

@[expose] def IsPCentralSubgroup (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  Nat.card H = p ∧ ∃ T : Subgroup G, Nat.card T = p ^ (Nat.card G).factorization p ∧
    H ≤ T ∧ H ≤ centralizer (T : Set G)

theorem map_conj_ofSylow {G : Type*} [Group G] {p : ℕ} (g : G) (S : Sylow p G) :
    ((g • S : Sylow p G) : Subgroup G) = (S : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Sylow.coe_subgroup_smul]
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  simp [Subgroup.mem_map]

theorem pCentral_exists_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T₀ : Subgroup G) (hT₀ : Nat.card T₀ = p ^ (Nat.card G).factorization p)
    (hZ : Nat.card ↥(T₀ ⊓ centralizer (T₀ : Set G)) = p) :
    ∀ H : Subgroup G, IsPCentralSubgroup p H →
      ∃ g : G, H = (T₀ ⊓ centralizer (T₀ : Set G)).map (MulAut.conj g).toMonoidHom := by
  let S₀ : Sylow p G := Sylow.ofCard T₀ hT₀
  rintro H ⟨hH, T, hT, hHT, hHc⟩
  let S : Sylow p G := Sylow.ofCard T hT
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ S
  have hS : (T : Subgroup G) = T₀.map (MulAut.conj g).toMonoidHom := by
    have := map_conj_ofSylow g S₀
    rw [hg] at this
    exact this
  refine ⟨g, ?_⟩
  have hmap : (T₀ ⊓ centralizer (T₀ : Set G)).map (MulAut.conj g).toMonoidHom =
      T ⊓ centralizer (T : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_centralizer, hS]
    rfl
  have hcard : Nat.card ↥((T₀ ⊓ centralizer (T₀ : Set G)).map (MulAut.conj g).toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hZ]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [hmap]
    exact le_inf hHT hHc
  · rw [hcard, hH]

theorem pCentral_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (T₀ : Subgroup G)
    (hT₀ : Nat.card T₀ = p ^ (Nat.card G).factorization p)
    (hZ : Nat.card ↥(T₀ ⊓ centralizer (T₀ : Set G)) = p) :
    (∃ H : Subgroup G, IsPCentralSubgroup p H) ∧
    ∀ H K : Subgroup G, IsPCentralSubgroup p H → IsPCentralSubgroup p K →
      ∃ g : G, H.map (MulAut.conj g).toMonoidHom = K := by
  have hcen := pCentral_exists_conj T₀ hT₀ hZ
  refine ⟨⟨T₀ ⊓ centralizer (T₀ : Set G), hZ, T₀, hT₀, inf_le_left, inf_le_right⟩, ?_⟩
  intro H K hH hK
  obtain ⟨g₁, rfl⟩ := hcen H hH
  obtain ⟨g₂, rfl⟩ := hcen K hK
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem isPCentralSubgroup_iff_exists_conj {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T₀ : Subgroup G) (hT₀ : Nat.card T₀ = p ^ (Nat.card G).factorization p)
    (hZ : Nat.card ↥(T₀ ⊓ centralizer (T₀ : Set G)) = p) {x : G}
    (hx : x ∈ T₀ ⊓ centralizer (T₀ : Set G)) (hxo : orderOf x = p) (H : Subgroup G) :
    IsPCentralSubgroup p H ↔ ∃ g : G, H = (zpowers x).map (MulAut.conj g).toMonoidHom := by
  have hZeq : T₀ ⊓ centralizer (T₀ : Set G) = zpowers x :=
    (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hx)
      (by rw [hZ, Nat.card_zpowers, hxo])).symm
  constructor
  · intro hH
    obtain ⟨g, hg⟩ := pCentral_exists_conj T₀ hT₀ hZ H hH
    exact ⟨g, by rw [hg, hZeq]⟩
  · rintro ⟨g, rfl⟩
    refine ⟨?_, T₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, Nat.card_zpowers, hxo]
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hT₀]
    · exact Subgroup.map_mono (zpowers_le.2 (mem_inf.1 hx).1)
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨t, ht, rfl⟩
      have hyc : y ∈ centralizer (T₀ : Set G) := (zpowers_le.2 (mem_inf.1 hx).2) hy
      have hty : t * y = y * t := mem_centralizer_iff.1 hyc t ht
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * t * g⁻¹ * (g * y * g⁻¹) = g * (t * y) * g⁻¹ := by group
        _ = g * (y * t) * g⁻¹ := by rw [hty]
        _ = g * y * g⁻¹ * (g * t * g⁻¹) := by group

theorem exists_subgroup_of_equiv {n : ℕ} {T : Type*} [Group T] {P : Subgroup (Equiv.Perm (Fin n))}
    (e : T ≃* P) {T₀ : Subgroup (Equiv.Perm (Fin n))} (hT₀P : T₀ ≤ P) {m c : ℕ}
    (hcard : Nat.card T₀ = m)
    (hZ : Nat.card ↥(T₀ ⊓ centralizer (T₀ : Set (Equiv.Perm (Fin n)))) = c) :
    ∃ T' : Subgroup T, Nat.card T' = m ∧ Nat.card ↥(T' ⊓ centralizer (T' : Set T)) = c := by
  let ι : T →* Equiv.Perm (Fin n) := P.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hrange : ι.range = P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map,
      range_subtype]
  let T' : Subgroup T := T₀.comap ι
  have hmapT : T'.map ι = T₀ := by
    rw [Subgroup.map_comap_eq, hrange]
    exact inf_eq_right.2 hT₀P
  have himg : ι '' (T' : Set T) = (T₀ : Set (Equiv.Perm (Fin n))) := by
    rw [← Subgroup.coe_map, hmapT]
  refine ⟨T', ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective hι, hmapT, hcard]
  · rw [← hZ, ← Subgroup.card_map_of_injective hι, Subgroup.map_inf _ _ _ hι, hmapT,
      map_centralizer_eq_inf hι, himg, hrange]
    have : T₀ ⊓ (P ⊓ centralizer (T₀ : Set (Equiv.Perm (Fin n)))) =
        T₀ ⊓ centralizer (T₀ : Set (Equiv.Perm (Fin n))) := by
      ext x
      simp only [mem_inf]
      exact ⟨fun ⟨a, _, c⟩ => ⟨a, c⟩, fun ⟨a, c⟩ => ⟨a, hT₀P a, c⟩⟩
    rw [this]


theorem sylowThreeOK_spec
    (h : sylowThreeOK = true) :
    ∃ T₀ : Subgroup (Equiv.Perm (Fin 275)), T₀ ≤ mclP ∧ Nat.card T₀ = 729 ∧
      Nat.card ↥(T₀ ⊓ centralizer (T₀ : Set (Equiv.Perm (Fin 275)))) = 3 ∧
      three₁ ∈ T₀ ⊓ centralizer (T₀ : Set (Equiv.Perm (Fin 275))) := by
  have hD : GroupData 275 mclP mclPGTbls mclGen mclSift := mcl_groupData
  have hn := hD.lt
  simp only [sylowThreeOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  set sg : Array Table := sylowThreeGens.toArray with hsg
  set E := mulClosureH 275 sg 800 with hE
  rw [Array.all_eq_true'] at h1
  simp only [Bool.and_eq_true] at h1
  have hg : ∀ x ∈ sg, permOK 275 x = true := fun x hx => (h1 x hx).1.1
  have hginv : ∀ x ∈ sg, invOK 275 x (invT 275 x) = true := fun x hx => (h1 x hx).2
  obtain ⟨hE1, hE2, hE3⟩ := enum_spec hn hg hginv h2 h3 h4
  set K := closure (tp 275 '' {x | x ∈ sg}) with hK
  have hKP : K ≤ mclP := by
    rw [hK, closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact (hD.sift _ _ (rep_tp (hg x hx))).1 (h1 x hx).1.2
  have hcard : Nat.card K = 729 := by rw [hE3]; exact h5
  have hrepE : ∀ k < E.1.size, Rep 275 E.1[k]! (tablePerm 275 E.1[k]!) := fun k hk => (hE1 k hk).1
  have hcentral : ∀ x : Equiv.Perm (Fin 275), (∀ g ∈ sg, tp 275 g * x = x * tp 275 g) →
      x ∈ centralizer (K : Set (Equiv.Perm (Fin 275))) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    have : K ≤ centralizer ({x} : Set (Equiv.Perm (Fin 275))) := by
      rw [hK, closure_le]
      rintro _ ⟨g, hg', rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact hx g hg'
    exact mem_centralizer_singleton_iff.1 (this hy)
  have hcomm : ∀ (e : Table) (x : Equiv.Perm (Fin 275)), Rep 275 e x →
      (sg.all fun g => commTT 275 e g) = true → ∀ g ∈ sg, tp 275 g * x = x * tp 275 g := by
    intro e x hx hall g hgs
    rw [Array.all_eq_true'] at hall
    exact ((commTT_iff hx (rep_tp (hg g hgs))).1 (hall g hgs)).symm
  set p : Table → Bool := fun e => sg.all fun g => commTT 275 e g with hp
  have hZ : ∀ x : Equiv.Perm (Fin 275), x ∈ K ⊓ centralizer (K : Set (Equiv.Perm (Fin 275))) ↔
      x ∈ (E.1.toList.filter p).map (tablePerm 275) := by
    intro x
    constructor
    · intro hx
      obtain ⟨hxK, hxc⟩ := mem_inf.1 hx
      obtain ⟨k, hk, hkrep⟩ := hE2 x hxK
      rw [List.mem_map]
      refine ⟨E.1[k]!, ?_, tablePerm_eq hkrep⟩
      rw [List.mem_filter]
      refine ⟨Array.mem_toList_iff.mpr (getElem!_mem_array hk), ?_⟩
      rw [hp]
      simp only
      rw [Array.all_eq_true']
      intro g hgs
      have hgK : tp 275 g ∈ K := subset_closure ⟨g, hgs, rfl⟩
      have := mem_centralizer_iff.1 hxc (tp 275 g) hgK
      exact (commTT_iff hkrep (rep_tp (hg g hgs))).2 this.symm
    · intro hx
      rw [List.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      rw [List.mem_filter] at he
      obtain ⟨hemem, hpe⟩ := he
      obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hemem)
      have hrk := hrepE k hk
      rw [getElem!_pos E.1 k hk] at hrk
      have hpe' : (sg.all fun g => commTT 275 E.1[k] g) = true := hpe
      refine mem_inf.2 ⟨?_, hcentral _ (hcomm _ _ hrk hpe')⟩
      have := (hE1 k hk).2
      rwa [getElem!_pos E.1 k hk] at this
  have hlist : ((E.1.toList.filter p).map (tablePerm 275)).Nodup := by
    have hall := nodup_of_hkeysDistinct (forall₂_tablePerm hrepE) h4
    exact hall.sublist ((List.filter_sublist).map _)
  have hZcard : Nat.card ↥(K ⊓ centralizer (K : Set (Equiv.Perm (Fin 275)))) = 3 := by
    classical
    have hset : ((K ⊓ centralizer (K : Set (Equiv.Perm (Fin 275))) : Subgroup _) :
        Set (Equiv.Perm (Fin 275))) =
        (((E.1.toList.filter p).map (tablePerm 275)).toFinset : Set (Equiv.Perm (Fin 275))) := by
      ext x
      simp only [SetLike.mem_coe, List.mem_toFinset]
      exact hZ x
    have h1' : Nat.card ↥(K ⊓ centralizer (K : Set (Equiv.Perm (Fin 275)))) =
        ((K ⊓ centralizer (K : Set (Equiv.Perm (Fin 275))) : Subgroup _) :
          Set (Equiv.Perm (Fin 275))).ncard := Nat.card_coe_set_eq _
    rw [h1', hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hlist, List.length_map]
    exact h6
  refine ⟨K, hKP, hcard, hZcard, ?_⟩
  have h0rep : Rep 275 (threeTbl 0) three₁ := rep_tp h0
  obtain ⟨j, hj, hjt⟩ := memT_spec hrepE h0rep h7
  have h3eq : three₁ = tablePerm 275 E.1[j]! := hjt
  refine (hZ three₁).2 ?_
  rw [List.mem_map]
  refine ⟨E.1[j]!, ?_, h3eq.symm⟩
  rw [List.mem_filter]
  refine ⟨Array.mem_toList_iff.mpr (getElem!_mem_array hj), ?_⟩
  rw [hp]
  simp only
  rw [Array.all_eq_true']
  intro g hgs
  rw [Array.all_eq_true'] at h8
  have h8g := (commTT_iff h0rep (rep_tp (hg g hgs))).1 (h8 g hgs)
  have hrj : Rep 275 E.1[j]! three₁ := h3eq ▸ hrepE j hj
  exact (commTT_iff hrj (rep_tp (hg g hgs))).2 h8g

theorem mcl_threeCentral_transitive
    (h : sylowThreeOK = true) :
    (∃ H : Subgroup CFSG.Blueprint.NativeSporadic.McL, IsPCentralSubgroup 3 H) ∧
    ∀ H K : Subgroup CFSG.Blueprint.NativeSporadic.McL, IsPCentralSubgroup 3 H →
      IsPCentralSubgroup 3 K → ∃ g : CFSG.Blueprint.NativeSporadic.McL,
        H.map (@MulAut.conj CFSG.Blueprint.NativeSporadic.McL inferInstance g).toMonoidHom = K := by
  obtain ⟨T₀, hT₀P, hcard, hZ, -⟩ := sylowThreeOK_spec h
  have hfac : (Nat.card CFSG.Blueprint.NativeSporadic.McL).factorization 3 = 6 := by
    rw [CFSG.Sporadic.McL.card_McL, show (898128000 : ℕ) = 3 ^ 6 * 1232000 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨T', hT'card, hT'Z⟩ := @exists_subgroup_of_equiv 275 CFSG.Blueprint.NativeSporadic.McL
    inferInstance mclP mclPermEquiv T₀ hT₀P 729 3 hcard hZ
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact @pCentral_conj CFSG.Blueprint.NativeSporadic.McL inferInstance inferInstance 3 this T'
    (by rw [hfac]; exact hT'card) hT'Z

end CFSG.Sporadic.Recognition.McLAS
