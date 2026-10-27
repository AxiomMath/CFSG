module

public import CFSG.Quasithin.Vol2.KGFactG2RuBasic
public import CFSG.Sporadic.Schreier.RuSEnum
public import Certificates.Certificate7163

public noncomputable section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native

theorem length_mul_card_inf_le' {G : Type*} [Group G] {S H : Subgroup G} [Finite S] {l : List G}
    (hl : ∀ s ∈ l, s ∈ S) (hp : l.Pairwise fun s u => s⁻¹ * u ∉ H) :
    l.length * Nat.card ↥(S ⊓ H) ≤ Nat.card S := by
  set K : Subgroup S := H.subgroupOf S
  have hK : Nat.card K = Nat.card ↥(S ⊓ H) := by
    rw [show K = (S ⊓ H).subgroupOf S from (Subgroup.inf_subgroupOf_left H S).symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hidx : l.length ≤ K.index := by
    let f : Fin l.length → S ⧸ K := fun i => QuotientGroup.mk ⟨l[i], hl _ (List.getElem_mem _)⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      have hmem : l[i]⁻¹ * l[j] ∈ H := by
        have := QuotientGroup.eq.1 hij
        rwa [Subgroup.mem_subgroupOf] at this
      rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact List.pairwise_iff_getElem.1 hp i j i.2 j.2 h hmem
      · refine List.pairwise_iff_getElem.1 hp j i j.2 i.2 h ?_
        simpa using H.inv_mem hmem
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin, ← Subgroup.index_eq_card] at this
  calc l.length * Nat.card ↥(S ⊓ H) = l.length * Nat.card K := by rw [hK]
    _ ≤ K.index * Nat.card K := Nat.mul_le_mul_right _ hidx
    _ = Nat.card S := by rw [mul_comm]; exact K.card_mul_index

theorem mem_normalizer_of_closure {G : Type*} [Group G] [Finite G] {s : Set G} {g : G}
    (h : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s) :
    g ∈ Subgroup.normalizer (Subgroup.closure s : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hle : Subgroup.closure s ≤ (Subgroup.closure s).comap (MulAut.conj g).toMonoidHom :=
    (Subgroup.closure_le _).2 fun x hx => by
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using h x hx
  have := hle hn
  simpa [Subgroup.mem_comap, MulAut.conj_apply] using this

section W

theorem g2WGen_comm {i j : ℕ} (hi : i < 6) (hj : j < 6) :
    g2WGen i * g2WGen j = g2WGen j * g2WGen i :=
  eq_of_eqA (rep_compA (rep_g2WGenA hi) (rep_g2WGenA hj))
    (rep_compA (rep_g2WGenA hj) (rep_g2WGenA hi)) (Certificates.certificate7163.1 i hi j hj)

theorem g2WGen_sq {i : ℕ} (hi : i < 6) : g2WGen i * g2WGen i = 1 :=
  eq_of_eqA (rep_compA (rep_g2WGenA hi) (rep_g2WGenA hi)) rep_idA
    (Certificates.certificate7163.2.1 i hi)

theorem g2WGen_zero : g2WGen 0 = ruZ :=
  eq_of_eqA (rep_g2WGenA (by norm_num)) rep_ruZ Certificates.certificate7163.2.2.1

theorem ruZ_mem_g2W : ruZ ∈ g2W := g2WGen_zero ▸ g2WGen_mem (by norm_num)

theorem exists_eq_g2WElt {x : Equiv.Perm (Fin 4060)} (hx : x ∈ g2W) :
    ∃ e < 64, x = g2WElt e := by
  have hstep : ∀ k < 6, ∀ e < 64, ∃ e' < 64, g2WGen k * g2WElt e = g2WElt e' := by
    intro k hk e he
    have h := Certificates.certificate7163.2.2.2.1 e he k hk
    obtain ⟨e', he', heq⟩ := eq_g2WElt_of_g2InW (rep_compA (rep_g2WGenA hk) (rep_g2WProd e)) h
    exact ⟨e', he', heq⟩
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, by norm_num, by simp [g2WElt]⟩
  | mul_left y hy z hz ih =>
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨e, he, rfl⟩ := ih
    obtain ⟨e', he', h⟩ := hstep k hk e he
    exact ⟨e', he', h⟩
  | inv_mul_cancel y hy z hz ih =>
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨e, he, rfl⟩ := ih
    rw [inv_eq_of_mul_eq_one_right (g2WGen_sq hk)]
    obtain ⟨e', he', h⟩ := hstep k hk e he
    exact ⟨e', he', h⟩

theorem g2W_comm {x y : Equiv.Perm (Fin 4060)} (hx : x ∈ g2W) (hy : y ∈ g2W) :
    x * y = y * x := by
  have h1 : ∀ k < 6, ∀ y ∈ g2W, g2WGen k * y = y * g2WGen k := by
    intro k hk y hy
    have hle : g2W ≤ Subgroup.centralizer {g2WGen k} := by
      rw [g2W, Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact g2WGen_comm hk hj
    exact Subgroup.mem_centralizer_iff.1 (hle hy) _ rfl
  have h2 : g2W ≤ Subgroup.centralizer {y} := by
    rw [g2W, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (h1 k hk y hy).symm
  exact (Subgroup.mem_centralizer_iff.1 (h2 hx) y rfl).symm

theorem g2W_sq {x : Equiv.Perm (Fin 4060)} (hx : x ∈ g2W) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    exact g2WGen_sq hk
  | one => simp
  | mul a b ha hb iha ihb =>
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [g2W_comm hb ha]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha =>
    rw [← mul_inv_rev, iha, inv_one]

theorem card_g2W_le : Nat.card g2W ≤ 64 := by
  have hsub : (g2W : Set (Equiv.Perm (Fin 4060))) ⊆
      (fun e : Fin 64 => g2WElt e) '' Set.univ := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := exists_eq_g2WElt hx
    exact ⟨⟨e, he⟩, Set.mem_univ _, rfl⟩
  calc Nat.card g2W = (g2W : Set (Equiv.Perm (Fin 4060))).ncard := Nat.card_coe_set_eq _
    _ ≤ ((fun e : Fin 64 => g2WElt e) '' Set.univ).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.univ : Set (Fin 64)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 64 := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem g2InW_of_mem {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (hg : g ∈ g2W) : g2InW t = true := by
  obtain ⟨e, he, rfl⟩ := exists_eq_g2WElt hg
  rw [g2InW, Array.any_eq_true]
  refine ⟨e, by simpa [g2WArr] using he, ?_⟩
  rw [← getElem!_pos g2WArr e (by simpa [g2WArr] using he)]
  exact (eqA_iff ht (rep_g2WArr he)).2 rfl

theorem g2NormW_of_mem {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (hg : g ∈ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060)))) : g2NormW t = true := by
  rw [g2NormW, allLt_iff]
  intro k hk
  refine g2InW_of_mem (rep_compA (rep_compA ht (rep_g2WGenA hk)) (rep_invCand' ht)) ?_
  exact (Subgroup.mem_normalizer_iff.1 hg _).1 (g2WGen_mem hk)

end W

section V

theorem g2V_le_g2W : g2V ≤ g2W := by
  rw [g2V, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  interval_cases k
  · rw [show g2VGen 0 = g2WGen 0 by simp [g2VGen]]
    exact g2WGen_mem (by norm_num)
  · exact mem_g2W_of_g2InW (rep_g2VGenA (by norm_num)) Certificates.certificate7163.2.2.2.2.1
  · exact mem_g2W_of_g2InW (rep_g2VGenA (by norm_num))
      Certificates.certificate7163.2.2.2.2.2.1

theorem exists_eq_g2VElt {x : Equiv.Perm (Fin 4060)} (hx : x ∈ g2V) :
    ∃ e < 8, x = g2VElt e := by
  have hstep : ∀ k < 3, ∀ e < 8, ∃ e' < 8, g2VGen k * g2VElt e = g2VElt e' := by
    intro k hk e he
    have h := Certificates.certificate7163.2.2.2.2.2.2.2.1 e he k hk
    obtain ⟨e', he', heq⟩ := eq_g2VElt_of_g2InV (rep_compA (rep_g2VGenA hk) (rep_g2VProd e)) h
    exact ⟨e', he', heq⟩
  have hsq : ∀ k < 3, g2VGen k * g2VGen k = 1 := fun k hk =>
    g2W_sq (g2V_le_g2W (g2VGen_mem hk))
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, by norm_num, by simp [g2VElt]⟩
  | mul_left y hy z hz ih =>
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨e, he, rfl⟩ := ih
    obtain ⟨e', he', h⟩ := hstep k hk e he
    exact ⟨e', he', h⟩
  | inv_mul_cancel y hy z hz ih =>
    obtain ⟨k, hk, rfl⟩ := hy
    obtain ⟨e, he, rfl⟩ := ih
    rw [inv_eq_of_mul_eq_one_right (hsq k hk)]
    obtain ⟨e', he', h⟩ := hstep k hk e he
    exact ⟨e', he', h⟩

theorem g2VElt_injective {i j : ℕ} (hi : i < 8) (hj : j < 8) (h : g2VElt i = g2VElt j) :
    i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := Certificates.certificate7163.2.2.2.2.2.2.1 i hi j hj hlt
    rw [(eqA_iff (rep_g2VArr hi) (rep_g2VArr hj)).2 h] at this
    exact Bool.noConfusion this
  · have := Certificates.certificate7163.2.2.2.2.2.2.1 j hj i hi hlt
    rw [(eqA_iff (rep_g2VArr hj) (rep_g2VArr hi)).2 h.symm] at this
    exact Bool.noConfusion this

theorem card_g2V : Nat.card g2V = 8 := by
  have hset : (g2V : Set (Equiv.Perm (Fin 4060))) = Set.range fun e : Fin 8 => g2VElt e := by
    ext x
    constructor
    · intro hx
      obtain ⟨e, he, rfl⟩ := exists_eq_g2VElt hx
      exact ⟨⟨e, he⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact g2VElt_mem e
  calc Nat.card g2V = (g2V : Set (Equiv.Perm (Fin 4060))).ncard := Nat.card_coe_set_eq _
    _ = (Set.range fun e : Fin 8 => g2VElt e).ncard := by rw [hset]
    _ = 8 := by
      rw [Set.ncard_range_of_injective (fun a b h => Fin.ext (g2VElt_injective a.2 b.2 h)),
        Nat.card_eq_fintype_card, Fintype.card_fin]

theorem normalizer_V_of_g2NormV {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (h : g2NormV t = true) : g ∈ Subgroup.normalizer (g2V : Set (Equiv.Perm (Fin 4060))) := by
  rw [g2NormV, allLt_iff] at h
  refine mem_normalizer_of_closure fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := hx
  exact mem_g2V_of_g2InV (rep_compA (rep_compA ht (rep_g2VGenA hk)) (rep_invCand' ht)) (h k hk)

end V

theorem card_ruC_inf_normalizer_le :
    Nat.card ↥(ruC ⊓ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060)))) ≤ 12288 := by
  set l := (List.range 20).map g2Rho with hl
  have hlC : ∀ s ∈ l, s ∈ ruC := by
    intro s hs
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hs
    exact g2CElt_mem _
  have hpair : l.Pairwise fun s u =>
      s⁻¹ * u ∉ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060))) := by
    rw [hl, List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {i j} hi hj hij hN => ?_
    rw [List.mem_range] at hi hj
    have hcheck := Certificates.certificate7163.2.2.2.2.2.2.2.2.1
    rw [g2RhoCheck, allLt_iff] at hcheck
    have h1 := (allLt_iff.1 (hcheck i hi)) j hj
    rw [decide_eq_true hij, Bool.not_true, Bool.false_or] at h1
    have hrep : Rep 4060 (compA 4060 (invCand 4060 (g2RhoA i)) (g2RhoA j))
        ((g2Rho i)⁻¹ * g2Rho j) :=
      rep_compA (rep_invCand' (rep_g2RhoA hi)) (rep_g2RhoA hj)
    rw [g2NormW_of_mem hrep hN] at h1
    exact Bool.false_ne_true h1
  have := length_mul_card_inf_le' hlC hpair
  rw [hl, List.length_map, List.length_range, card_ruC] at this
  omega

theorem card_ruP_inf_normalizer_le :
    Nat.card ↥(ruP ⊓ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060)))) ≤ 774144 := by
  set N := ruP ⊓ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060))) with hN
  set N' : Subgroup (ConjAct (Equiv.Perm (Fin 4060))) := N.map ConjAct.toConjAct.toMonoidHom
  have hcardN : Nat.card N' = Nat.card N :=
    Nat.card_congr (N.equivMapOfInjective _ ConjAct.toConjAct.injective).toEquiv.symm
  have horb : MulAction.orbit N' ruZ ⊆ (g2W : Set (Equiv.Perm (Fin 4060))) \ {1} := by
    rintro _ ⟨⟨n, hn⟩, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hn
    have hmN : m ∈ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060))) := hm.2
    change ConjAct.toConjAct m • ruZ ∈ _
    rw [ConjAct.toConjAct_smul]
    refine ⟨(Subgroup.mem_normalizer_iff.1 hmN _).1 ruZ_mem_g2W, ?_⟩
    rw [Set.mem_singleton_iff]
    intro h1
    have hz : ruZ = 1 := by
      have := congrArg (fun x => m⁻¹ * x * m) h1
      simpa [mul_assoc] using this
    exact ruZ_ne_one hz
  have hW1 : ((g2W : Set (Equiv.Perm (Fin 4060))) \ {1}).ncard ≤ 63 := by
    have h1 := Set.ncard_sdiff_singleton_of_mem (s := (g2W : Set (Equiv.Perm (Fin 4060))))
      g2W.one_mem
    have h2 : (g2W : Set (Equiv.Perm (Fin 4060))).ncard ≤ 64 := by
      rw [← Nat.card_coe_set_eq]
      exact card_g2W_le
    omega
  have hidx : (MulAction.stabilizer N' ruZ).index ≤ 63 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard horb (Set.toFinite _)).trans hW1
  have hstab : Nat.card (MulAction.stabilizer N' ruZ) ≤ 12288 := by
    refine le_trans ?_ card_ruC_inf_normalizer_le
    have key : ∀ x : MulAction.stabilizer N' ruZ,
        ConjAct.ofConjAct ((x : N') : ConjAct (Equiv.Perm (Fin 4060))) ∈
          ruC ⊓ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060))) := by
      rintro ⟨⟨c, hc⟩, hx⟩
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hc
      have hxz : ConjAct.toConjAct m • ruZ = ruZ := hx
      rw [ConjAct.toConjAct_smul] at hxz
      simp only [MulEquiv.coe_toMonoidHom, ConjAct.ofConjAct_toConjAct]
      refine ⟨?_, hm.2⟩
      rw [ruC_eq_centralizer]
      refine ⟨hm.1, Subgroup.mem_centralizer_iff.2 ?_⟩
      rintro _ rfl
      calc ruZ * m = m * ruZ * m⁻¹ * m := by rw [hxz]
        _ = m * ruZ := by group
    let f : MulAction.stabilizer N' ruZ →
        ↥(ruC ⊓ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060)))) := fun x => ⟨_, key x⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (ConjAct.ofConjAct.injective h1))
    exact Nat.card_le_card_of_injective f hf
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer N' ruZ)
  rw [hcardN] at hmul
  calc Nat.card N = Nat.card (MulAction.stabilizer N' ruZ) * (MulAction.stabilizer N' ruZ).index :=
        hmul.symm
    _ ≤ 12288 * 63 := Nat.mul_le_mul hstab hidx
    _ = 774144 := by norm_num

theorem normalizer_V_of_mem_ruS
    {s : Equiv.Perm (Fin 4060)} (hs : s ∈ ruS)
    (hW : s ∈ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060)))) :
    s ∈ Subgroup.normalizer (g2V : Set (Equiv.Perm (Fin 4060))) := by
  refine ruS_forall (p := fun s => !g2NormW s || g2NormV s)
    (P := fun g => g ∈ Subgroup.normalizer (g2W : Set (Equiv.Perm (Fin 4060))) →
      g ∈ Subgroup.normalizer (g2V : Set (Equiv.Perm (Fin 4060))))
    (fun t g ht hp hg => ?_) Certificates.certificate7163.2.2.2.2.2.2.2.2.2 s hs hW
  rw [g2NormW_of_mem ht hg, Bool.not_true, Bool.false_or] at hp
  exact normalizer_V_of_g2NormV ht hp

end CFSG.Quasithin.H13.Ch4.G2Ru
