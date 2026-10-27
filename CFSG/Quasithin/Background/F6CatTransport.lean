module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace F6

variable {D E : Type*} [Group D] [Group E] {G₁ G₂ : Subgroup D}

theorem isSolvable_perm_three : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  have hc : ∀ a b : ↥(alternatingGroup (Fin 3)), a * b = b * a := by
    have key : ∀ u v : Equiv.Perm (Fin 3), (Equiv.Perm.sign u = 1 ∧ Equiv.Perm.sign v = 1) →
        u * v = v * u := by
      decide +kernel
    intro a b
    exact Subtype.ext (key _ _ ⟨Equiv.Perm.mem_alternatingGroup.mp a.2,
      Equiv.Perm.mem_alternatingGroup.mp b.2⟩)
  have : Group.IsSolvable ↥(alternatingGroup (Fin 3)) := Group.isSolvable_of_comm hc
  have hq : Nat.card (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) = 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (alternatingGroup (Fin 3))
    have hS : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hA : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    rw [hS, hA] at h1
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) := isCyclic_of_prime_card hq
  have : Group.IsSolvable (Equiv.Perm (Fin 3) ⧸ alternatingGroup (Fin 3)) :=
    Group.isSolvable_of_comm fun a b => IsCyclic.isMulCommutative.is_comm.comm a b
  exact Group.isSolvable_of_subgroup_quotient (alternatingGroup (Fin 3))

theorem isSolvable_of_quotient_pCore {H : Type*} [Group H] [Finite H]
    (e : H ⧸ Open.pCore 2 H ≃* Equiv.Perm (Fin 3)) : Group.IsSolvable H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(Open.pCore 2 H) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := H) 2).isNilpotent
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := isSolvable_perm_three
  have : Group.IsSolvable (H ⧸ Open.pCore 2 H) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : (Open.pCore 2 H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  exact Group.isSolvable_of_subgroup_quotient (Open.pCore 2 H)

theorem isSolvable_vertex_left [Finite D] (h : IsGoldschmidtTriple G₁ G₂) :
    Group.IsSolvable ↥G₁ :=
  isSolvable_of_quotient_pCore h.quotient₁.some

theorem isSolvable_vertex_right [Finite D] (h : IsGoldschmidtTriple G₁ G₂) :
    Group.IsSolvable ↥G₂ :=
  isSolvable_of_quotient_pCore h.quotient₂.some

noncomputable def mulEquivMapOfInjOn {H : Subgroup D} (f : D →* E)
    (hf : ∀ x ∈ H, f x = 1 → x = 1) : ↥H ≃* ↥(H.map f) := by
  let ψ : ↥H →* E := f.comp H.subtype
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact Subtype.ext (hf x x.2 hx)
  exact (MonoidHom.ofInjective hψ).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

theorem goldschmidtTriple_map_of_injOn [Finite D] (h : IsGoldschmidtTriple G₁ G₂)
    (f : D →* E) (hf : Function.Surjective f) (h₁ : ∀ x ∈ G₁, f x = 1 → x = 1)
    (h₂ : ∀ x ∈ G₂, f x = 1 → x = 1) (hinf : G₁.map f ⊓ G₂.map f = (G₁ ⊓ G₂).map f) :
    IsGoldschmidtTriple (G₁.map f) (G₂.map f) where
  gen := by
    rw [← Subgroup.map_sup, h.gen, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hf
  quotient₁ := by
    let e := mulEquivMapOfInjOn f h₁
    have hker : IsPGroup 2 e.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
      exact IsPGroup.of_bot
    exact gold_isoS3_of_surjective_kernel e.toMonoidHom e.surjective hker h.quotient₁.some
  quotient₂ := by
    let e := mulEquivMapOfInjOn f h₂
    have hker : IsPGroup 2 e.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
      exact IsPGroup.of_bot
    exact gold_isoS3_of_surjective_kernel e.toMonoidHom e.surjective hker h.quotient₂.some
  sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T, hT⟩ := h.sylow
    refine ⟨T.mapSurjective hf, ?_⟩
    rw [Sylow.coe_mapSurjective, hT, hinf]

theorem goldschmidtTriple_map_mulEquiv [Finite D] (h : IsGoldschmidtTriple G₁ G₂)
    (e : D ≃* E) : IsGoldschmidtTriple (G₁.map e.toMonoidHom) (G₂.map e.toMonoidHom) :=
  goldschmidtTriple_map_of_injOn h e.toMonoidHom e.surjective
    (fun _ _ hx => e.injective (hx.trans (map_one e).symm))
    (fun _ _ hx => e.injective (hx.trans (map_one e).symm))
    (Subgroup.map_inf_eq _ _ _ e.injective).symm

theorem inf_eq_bot_of_card_eq_three [Finite D]
    (h : IsGoldschmidtTriple G₁ G₂) (hns : ¬ Group.IsSolvable D) {N : Subgroup D} [N.Normal]
    (hN : Nat.card N = 3) : N ⊓ G₁ = ⊥ := by
  by_contra hne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNG : N ≤ G₁ := by
    have hdvd : Nat.card ↥(N ⊓ G₁) ∣ 3 := hN ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd (Subgroup.card_eq_one.mp h1) hne
    · exact (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hN, h3])) ▸ inf_le_right
  set T := G₁ ⊓ G₂ with hTdef
  have hT2 : IsPGroup 2 ↥T := h.isPGroup_inf
  have hNT : N ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hd3 : orderOf x ∣ 3 := hN ▸ Subgroup.orderOf_dvd_natCard N hx.1
    obtain ⟨k, hk⟩ := hT2 ⟨x, hx.2⟩
    have hd2 : orderOf x ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left hd3 (Nat.Coprime.pow_right k (by norm_num))) hd2)
  have hG₁ : G₁ = N ⊔ T := by
    refine (Subgroup.eq_of_le_of_card_ge (sup_le hNG inf_le_left) ?_).symm
    have h3 : Nat.card ↥G₁ = 3 * Nat.card ↥T := by
      have := Subgroup.relIndex_mul_card (H := T) (K := G₁)
      rw [inf_eq_left.mpr inf_le_left, h.relIndex_inf_left] at this
      rw [← this]
    obtain ⟨k, hk⟩ := hT2.exists_card_eq
    have hcop : Nat.Coprime 3 (Nat.card ↥T) := by
      rw [hk]
      exact Nat.Coprime.pow_right k (by norm_num)
    have hdvd : 3 * Nat.card ↥T ∣ Nat.card ↥(N ⊔ T) :=
      hcop.mul_dvd_of_dvd_of_dvd (hN ▸ Subgroup.card_dvd_of_le le_sup_left)
        (Subgroup.card_dvd_of_le le_sup_right)
    rw [h3]
    exact Nat.le_of_dvd Nat.card_pos hdvd
  have htop : N ⊔ G₂ = ⊤ := by
    rw [← h.gen, hG₁, sup_assoc, sup_eq_right.mpr (inf_le_right : T ≤ G₂)]
  have : Group.IsSolvable ↥G₂ := isSolvable_vertex_right h
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp G₂.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ ((G₂ ⊔ N : Subgroup D) : Set D) := by
      rw [sup_comm, htop]
      exact Subgroup.mem_top x
    rw [Subgroup.mul_normal] at hx
    obtain ⟨g, hg, n, hn, rfl⟩ := hx
    refine ⟨⟨g, hg⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
  have : Group.IsSolvable (D ⧸ N) := Group.isSolvable_of_surjective hsurj
  have hNc : ∀ a b : ↥N, a * b = b * a := by
    have : IsCyclic ↥N := isCyclic_of_prime_card hN
    exact fun a b => IsCyclic.isMulCommutative.is_comm.comm a b
  have : Group.IsSolvable ↥N := Group.isSolvable_of_comm hNc
  exact hns (Group.isSolvable_of_subgroup_quotient N)

theorem goldschmidtTriple_map_quotient_of_card_eq_three [Finite D]
    (h : IsGoldschmidtTriple G₁ G₂) (hns : ¬ Group.IsSolvable D) {N : Subgroup D} [N.Normal]
    (hN : Nat.card N = 3) :
    (∀ x ∈ G₁, QuotientGroup.mk' N x = 1 → x = 1) ∧
      (∀ x ∈ G₂, QuotientGroup.mk' N x = 1 → x = 1) ∧
      IsGoldschmidtTriple (G₁.map (QuotientGroup.mk' N)) (G₂.map (QuotientGroup.mk' N)) := by
  have hinj : ∀ {G : Subgroup D}, N ⊓ G = ⊥ → ∀ x ∈ G, QuotientGroup.mk' N x = 1 → x = 1 := by
    intro G hG x hx h1
    have : x ∈ N ⊓ G := ⟨(QuotientGroup.eq_one_iff x).mp h1, hx⟩
    rw [hG, Subgroup.mem_bot] at this
    exact this
  have h₁ := hinj (inf_eq_bot_of_card_eq_three h hns hN)
  have h₂ := hinj (inf_eq_bot_of_card_eq_three h.symm hns hN)
  refine ⟨h₁, h₂, goldschmidtTriple_map_of_injOn h (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) h₁ h₂ ?_⟩
  set f := QuotientGroup.mk' N
  set T := G₁ ⊓ G₂
  refine le_antisymm ?_ (Subgroup.map_inf_le _ _ _)
  set I := G₁.map f ⊓ G₂.map f
  have hTI : T.map f ≤ I := Subgroup.map_inf_le _ _ _
  have hcT : Nat.card ↥(T.map f) = Nat.card ↥T :=
    Nat.card_congr (mulEquivMapOfInjOn f fun x hx => h₁ x (Subgroup.mem_inf.mp hx).1).toEquiv.symm
  have hc₁ : Nat.card ↥(G₁.map f) = Nat.card ↥G₁ :=
    Nat.card_congr (mulEquivMapOfInjOn f h₁).toEquiv.symm
  have hc₂ : Nat.card ↥(G₂.map f) = Nat.card ↥G₂ :=
    Nat.card_congr (mulEquivMapOfInjOn f h₂).toEquiv.symm
  have h3₁ : Nat.card ↥G₁ = 3 * Nat.card ↥T := by
    have := Subgroup.relIndex_mul_card (H := T) (K := G₁)
    rw [inf_eq_left.mpr inf_le_left, h.relIndex_inf_left] at this
    rw [← this]
  have h3₂ : Nat.card ↥G₂ = 3 * Nat.card ↥T := by
    have := Subgroup.relIndex_mul_card (H := T) (K := G₂)
    rw [inf_eq_left.mpr inf_le_right, h.relIndex_inf_right] at this
    rw [← this]
  have hdI : Nat.card ↥(T.map f) ∣ Nat.card ↥I := Subgroup.card_dvd_of_le hTI
  have hId : Nat.card ↥I ∣ Nat.card ↥(G₁.map f) := Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨a, ha⟩ := hdI
  obtain ⟨b, hb⟩ := hId
  have hTpos : 0 < Nat.card ↥T := Nat.card_pos
  have hab : a * b = 3 := by
    have e1 : Nat.card ↥T * 3 = Nat.card ↥T * (a * b) := by
      calc Nat.card ↥T * 3 = Nat.card ↥(G₁.map f) := by rw [hc₁, h3₁, mul_comm]
        _ = Nat.card ↥T * (a * b) := by rw [hb, ha, hcT, mul_assoc]
    exact (Nat.eq_of_mul_eq_mul_left hTpos e1).symm
  rcases Nat.prime_three.eq_one_or_self_of_dvd a ⟨b, hab.symm⟩ with ha1 | ha3
  ·
    subst ha1
    exact (Subgroup.eq_of_le_of_card_ge hTI (by rw [ha, mul_one])).symm.le
  ·
    have hb1 : b = 1 := by
      subst ha3
      omega
    subst hb1
    exfalso
    have hI₁ : I = G₁.map f := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hb, mul_one])
    have hle : G₁.map f ≤ G₂.map f := hI₁ ▸ inf_le_right
    have heq : G₁.map f = G₂.map f :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc₁, hc₂, h3₁, h3₂])
    have htop : G₁.map f = ⊤ := by
      have h1 : G₁.map f ⊔ G₂.map f = ⊤ := by
        rw [← Subgroup.map_sup, h.gen, ← MonoidHom.range_eq_map]
        exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
      rw [← heq, sup_idem] at h1
      exact h1
    have : Group.IsSolvable ↥G₁ := isSolvable_vertex_left h
    have hsurj : Function.Surjective (f.comp G₁.subtype) := by
      intro q
      have hq : q ∈ G₁.map f := htop ▸ Subgroup.mem_top q
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨⟨x, hx⟩, rfl⟩
    have : Group.IsSolvable (D ⧸ N) := Group.isSolvable_of_surjective hsurj
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : IsCyclic ↥N := isCyclic_of_prime_card hN
    have : Group.IsSolvable ↥N :=
      Group.isSolvable_of_comm fun a b => IsCyclic.isMulCommutative.is_comm.comm a b
    exact hns (Group.isSolvable_of_subgroup_quotient N)

end F6

end CFSG.Quasithin
