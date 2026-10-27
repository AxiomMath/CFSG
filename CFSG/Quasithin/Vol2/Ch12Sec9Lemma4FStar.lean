module

public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Fact
public import CFSG.RankThree.PartOne.S12.TerminalWeylPerm

public section

namespace CFSG.Quasithin.H13

namespace L1294F

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem le_genFittingFStar_of_commute {N : Subgroup G}
    (h : ∀ n ∈ N, ∀ f ∈ genFittingFStar G, n * f = f * n) : N ≤ genFittingFStar G :=
  fun n hn => CFSG.Adapters.generalized_fitting_self_centralizing G
    (Subgroup.mem_centralizer_iff.2 fun f hf => (h n hn f hf).symm)

omit [Finite G] in
theorem commute_of_inf_eq_bot {N M : Subgroup G} (hNM : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N)
    (hMN : ∀ n ∈ N, ∀ m ∈ M, n * m * n⁻¹ ∈ M) (h : N ⊓ M = ⊥) {n f : G} (hn : n ∈ N)
    (hf : f ∈ M) : n * f = f * n := by
  have h1 : n * f * n⁻¹ * f⁻¹ ∈ N ⊓ M := by
    refine ⟨?_, ?_⟩
    · have := N.mul_mem hn (hNM f hf n⁻¹ (N.inv_mem hn))
      simpa [mul_assoc] using this
    · exact M.mul_mem (hMN n hn f hf) (M.inv_mem hf)
  rw [h, Subgroup.mem_bot] at h1
  calc n * f = n * f * n⁻¹ * f⁻¹ * (f * n) := by group
    _ = f * n := by rw [h1, one_mul]

theorem genFittingFStar_le_of_normal (hS : IsSimpleGroup ↥(genFittingFStar G)) {N : Subgroup G}
    (hN : N.Normal) (hN1 : N ≠ ⊥) : genFittingFStar G ≤ N := by
  set F := genFittingFStar G with hF
  have hFn : F.Normal := A7Mod.genFittingFStar_normal' G
  have hNF : (N.subgroupOf F).Normal := Subgroup.Normal.subgroupOf hN F
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf F) with h | h
  · exfalso
    apply hN1
    have hinf : N ⊓ F = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxN, hxF⟩
      have : (⟨x, hxF⟩ : F) ∈ N.subgroupOf F := Subgroup.mem_subgroupOf.2 hxN
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
    have hle : N ≤ F := le_genFittingFStar_of_commute fun n hn f hf =>
      commute_of_inf_eq_bot (fun m _ x hx => hN.conj_mem x hx m)
        (fun x _ m hm => hFn.conj_mem m hm x) hinf hn hf
    rw [eq_bot_iff]
    intro x hx
    rw [← hinf]
    exact ⟨hx, hle hx⟩
  · intro x hx
    have : (⟨x, hx⟩ : F) ∈ N.subgroupOf F := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

omit [Finite G] in
theorem exists_mul_of_mem_sup {L L' : Subgroup G} (hc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    {x : G} (hx : x ∈ L ⊔ L') : ∃ a ∈ L, ∃ b ∈ L', x = a * b := by
  let K : Subgroup G :=
    { carrier := {x | ∃ a ∈ L, ∃ b ∈ L', x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', L.mul_mem ha ha', b * b', L'.mul_mem hb hb', ?_⟩
        rw [mul_assoc, ← mul_assoc b, ← hc a' ha' b hb]
        group
      one_mem' := ⟨1, L.one_mem, 1, L'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, L.inv_mem ha, b⁻¹, L'.inv_mem hb, ?_⟩
        rw [mul_inv_rev, (hc a⁻¹ (L.inv_mem ha) b⁻¹ (L'.inv_mem hb)).symm] }
  have hLK : L ≤ K := fun a ha => ⟨a, ha, 1, L'.one_mem, by simp⟩
  have hL'K : L' ≤ K := fun b hb => ⟨1, L.one_mem, b, hb, by simp⟩
  exact (sup_le hLK hL'K) hx

omit [Finite G] in
theorem eq_one_of_commute {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 5))
    {a : G} (ha : a ∈ L) (hcomm : ∀ y ∈ L, a * y = y * a) : a = 1 := by
  have hZ : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  have hmem : eL ⟨a, ha⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := eL.surjective z
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm y y.2).symm
  rw [hZ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hmem
  exact congrArg Subtype.val hmem

omit [Finite G] in
theorem card_eq_sixty {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 5)) :
    Nat.card L = 60 := by
  rw [Nat.card_congr eL.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

omit [Finite G] in
theorem eq_one_of_pow_seven_mem {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 5))
    {a : G} (ha : a ∈ L) (h7 : a ^ 7 = 1) : a = 1 := by
  have h1 : orderOf (⟨a, ha⟩ : L) ∣ 7 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h7))
  have h2 : orderOf (⟨a, ha⟩ : L) ∣ 60 := card_eq_sixty eL ▸ orderOf_dvd_natCard _
  have h3 : orderOf (⟨a, ha⟩ : L) = 1 :=
    Nat.dvd_one.1 ((by norm_num : Nat.gcd 7 60 = 1) ▸ Nat.dvd_gcd h1 h2)
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)

variable {L L' : Subgroup G}

omit [Finite G] in
theorem conj_mem_of_mem_sup (hc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) {f : G} (hf : f ∈ L ⊔ L')
    {l : G} (hl : l ∈ L) : f * l * f⁻¹ ∈ L := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hf
  have hbl : b * l * b⁻¹ = l := by
    rw [← hc l hl b hb]
    group
  have e : a * b * l * (a * b)⁻¹ = a * (b * l * b⁻¹) * a⁻¹ := by group
  rw [e, hbl]
  exact L.mul_mem (L.mul_mem ha hl) (L.inv_mem ha)

theorem map_conj_eq_or_eq (hF : genFittingFStar G = L ⊔ L')
    (hc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a)
    (eL : ↥L ≃* alternatingGroup (Fin 5)) (eL' : ↥L' ≃* alternatingGroup (Fin 5)) (g : G) :
    L.map (MulAut.conj g).toMonoidHom = L ∨ L.map (MulAut.conj g).toMonoidHom = L' := by
  set F := L ⊔ L' with hFdef
  have hFn : F.Normal := hF ▸ A7Mod.genFittingFStar_normal' G
  set M := L.map (MulAut.conj g).toMonoidHom with hM
  have hmemM : ∀ x, x ∈ M ↔ g⁻¹ * x * g ∈ L := fun x => by
    rw [hM, Subgroup.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hl
    · intro h
      exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hLF : L ≤ F := le_sup_left
  have hMF : M ≤ F := by
    intro x hx
    rw [hmemM] at hx
    have := hFn.conj_mem _ (hLF hx) g
    simpa [mul_assoc] using this
  have hMnorm : ∀ f ∈ F, ∀ m ∈ M, f * m * f⁻¹ ∈ M := by
    intro f hf m hm
    rw [hmemM] at hm ⊢
    have hf' : g⁻¹ * f * g ∈ F := by simpa [mul_assoc] using hFn.conj_mem f hf g⁻¹
    have := conj_mem_of_mem_sup hc hf' hm
    simpa [mul_assoc] using this
  have hLnorm : ∀ f ∈ F, ∀ l ∈ L, f * l * f⁻¹ ∈ L := fun f hf l hl =>
    conj_mem_of_mem_sup hc hf hl
  have hsimple : IsSimpleGroup ↥L := eL.isSimpleGroup
  have hnorm : ((M ⊓ L).subgroupOf L).Normal := ⟨fun x hx l => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hMnorm _ (hLF l.2) _ hx.1, L.mul_mem (L.mul_mem l.2 hx.2) (L.inv_mem l.2)⟩⟩
  have hcardM : Nat.card M = 60 := by
    rw [hM, Subgroup.card_map_of_injective (MulAut.conj g).injective, card_eq_sixty eL]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((M ⊓ L).subgroupOf L) with h | h
  · right
    have hinf : M ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : L) ∈ (M ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.2 hx
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
    have hcomm : ∀ m ∈ M, ∀ l ∈ L, m * l = l * m := fun m hm l hl =>
      commute_of_inf_eq_bot (fun l' hl' m' hm' => hMnorm l' (hLF hl') m' hm')
        (fun m' hm' l' hl' => hLnorm m' (hMF hm') l' hl') hinf hm hl
    have hML' : M ≤ L' := by
      intro m hm
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc (hMF hm)
      have ha1 : a = 1 := by
        refine eq_one_of_commute eL ha fun y hy => ?_
        have h1 := hcomm _ hm y hy
        have h2 := hc y hy b hb
        have : a * y * b = y * a * b := by
          calc a * y * b = a * (y * b) := by group
            _ = a * (b * y) := by rw [h2]
            _ = a * b * y := by group
            _ = y * (a * b) := h1
            _ = y * a * b := by group
        exact mul_right_cancel this
      rw [ha1, one_mul]
      exact hb
    exact (Subgroup.eq_of_le_of_card_ge hML' (by rw [hcardM, card_eq_sixty eL'])).symm.symm
  · left
    have hLM : L ≤ M := by
      intro x hx
      have : (⟨x, hx⟩ : L) ∈ (M ⊓ L).subgroupOf L := by
        rw [h]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 this).1
    exact (Subgroup.eq_of_le_of_card_ge hLM (by rw [hcardM, card_eq_sixty eL])).symm

theorem mem_normalizer_of_pow_seven (hF : genFittingFStar G = L ⊔ L')
    (hc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) (hinf : L ⊓ L' = ⊥)
    (eL : ↥L ≃* alternatingGroup (Fin 5)) (eL' : ↥L' ≃* alternatingGroup (Fin 5)) {g : G}
    (hg : g ^ 7 = 1) : g ∈ Subgroup.normalizer (L : Set G) := by
  have hmem : ∀ {K : Subgroup G} {h : G}, K.map (MulAut.conj h).toMonoidHom = K →
      h ∈ Subgroup.normalizer (K : Set G) := fun {K h} hK =>
    Subgroup.mem_normalizer_iff.2 fun x => by
      constructor
      · intro hx
        rw [← hK]
        exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
      · intro hx
        rw [← hK] at hx
        obtain ⟨k, hk, hkx⟩ := hx
        have : k = x := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkx
          simpa using hkx
        rwa [← this]
  rcases map_conj_eq_or_eq hF hc eL eL' g with h | h
  · exact hmem h
  · have hc' : ∀ a ∈ L', ∀ b ∈ L, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    rcases map_conj_eq_or_eq (L := L') (L' := L) (by rw [hF, sup_comm]) hc' eL' eL g with
      h' | h'
    · exfalso
      have hLL : L = L' :=
        Subgroup.map_injective (MulAut.conj g).injective (h.trans h'.symm)
      have h60 := card_eq_sixty eL
      have hbot : L = ⊥ := by simpa [← hLL] using hinf
      rw [hbot, Subgroup.card_bot] at h60
      norm_num at h60
    ·
      have hg2 : (L.map (MulAut.conj (g ^ 2)).toMonoidHom) = L := by
        have hcomp : (MulAut.conj (g ^ 2)).toMonoidHom =
            (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom :=
          MonoidHom.ext fun x => by simp [MulAut.conj_apply, pow_two, mul_assoc]
        rw [hcomp, ← Subgroup.map_map, h, h']
      have hgg : g = (g ^ 2) ^ 4 := by
        rw [← pow_mul, show 2 * 4 = 7 + 1 from rfl, pow_succ, hg, one_mul]
      rw [hgg]
      exact Subgroup.pow_mem _ (hmem hg2) 4

omit [Finite G] in
theorem commute_of_pow_seven (eL : ↥L ≃* alternatingGroup (Fin 5)) {g : G}
    (hgN : g ∈ Subgroup.normalizer (L : Set G)) (hg : g ^ 7 = 1) :
    ∀ y ∈ L, g * y = y * g := by
  obtain ⟨π, -, hπ⟩ := CFSG.RankThree.PartOne.TerminalPerm.exists_pi_of_equiv eL
    (Subgroup.le_normalizer (H := L))
    (fun g hg y hy => (Subgroup.mem_normalizer_iff.1 hg y).1 hy)
  have h1 : π ⟨g, hgN⟩ = 1 := by
    have h7 : π ⟨g, hgN⟩ ^ 7 = 1 := by
      rw [← map_pow]
      have : (⟨g, hgN⟩ : Subgroup.normalizer (L : Set G)) ^ 7 = 1 := Subtype.ext (by simpa using hg)
      rw [this, map_one]
    have hd1 : orderOf (π ⟨g, hgN⟩) ∣ 7 := orderOf_dvd_of_pow_eq_one h7
    have hd2 : orderOf (π ⟨g, hgN⟩) ∣ 120 := by
      have := orderOf_dvd_natCard (π ⟨g, hgN⟩)
      rwa [Nat.card_perm, Nat.card_fin] at this
    exact orderOf_eq_one_iff.1
      (Nat.dvd_one.1 ((by norm_num : Nat.gcd 7 120 = 1) ▸ Nat.dvd_gcd hd1 hd2))
  exact hπ ⟨g, hgN⟩ h1

theorem eq_one_of_pow_seven (hF : genFittingFStar G = L ⊔ L')
    (hc : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) (hinf : L ⊓ L' = ⊥)
    (eL : ↥L ≃* alternatingGroup (Fin 5)) (eL' : ↥L' ≃* alternatingGroup (Fin 5)) {g : G}
    (hg : g ^ 7 = 1) : g = 1 := by
  have hc' : ∀ a ∈ L', ∀ b ∈ L, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hinf' : L' ⊓ L = ⊥ := by rw [inf_comm, hinf]
  have hF' : genFittingFStar G = L' ⊔ L := by rw [hF, sup_comm]
  have h1 := commute_of_pow_seven eL (mem_normalizer_of_pow_seven hF hc hinf eL eL' hg) hg
  have h2 := commute_of_pow_seven eL' (mem_normalizer_of_pow_seven hF' hc' hinf' eL' eL hg) hg
  have hgF : g ∈ genFittingFStar G := by
    refine CFSG.Adapters.generalized_fitting_self_centralizing G
      (Subgroup.mem_centralizer_iff.2 fun f hf => ?_)
    rw [hF] at hf
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hf
    calc a * b * g = a * (b * g) := by group
      _ = a * (g * b) := by rw [h2 b hb]
      _ = (a * g) * b := by group
      _ = (g * a) * b := by rw [h1 a ha]
      _ = g * (a * b) := by group
  rw [hF] at hgF
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hc hgF
  have hab : (a * b) ^ 7 = a ^ 7 * b ^ 7 := (Commute.mul_pow (hc a ha b hb) 7)
  rw [hab] at hg
  have ha7 : a ^ 7 ∈ L ⊓ L' := by
    refine ⟨L.pow_mem ha 7, ?_⟩
    have : a ^ 7 = (b ^ 7)⁻¹ := eq_inv_of_mul_eq_one_left hg
    rw [this]
    exact L'.inv_mem (L'.pow_mem hb 7)
  rw [hinf, Subgroup.mem_bot] at ha7
  have ha1 := eq_one_of_pow_seven_mem eL ha ha7
  rw [ha1, one_pow, one_mul] at hg
  rw [ha1, eq_one_of_pow_seven_mem eL' hb hg, one_mul]

end L1294F

end CFSG.Quasithin.H13
