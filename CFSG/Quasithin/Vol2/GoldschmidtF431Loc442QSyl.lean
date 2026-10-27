module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Syl

public section

namespace CFSG.Quasithin.Loc442Q

open CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431

universe u v

section Basic

variable {G : Type*} [Group G]

theorem exists_sylowTwo_ge [Finite G] {P H : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ S : Subgroup G, IsSylowTwoOf S H ∧ P ≤ S := by
  have hP' : IsPGroup 2 (P.subgroupOf H) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hQS : (Q : Subgroup H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  refine ⟨(Q : Subgroup H).map H.subtype, ⟨hQS, Q.isPGroup'.map H.subtype, ?_⟩, ?_⟩
  · change ¬ 2 ∣ (Subgroup.comap H.subtype ((Q : Subgroup H).map H.subtype)).index
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact Sylow.not_dvd_index Q
  · intro x hx
    have := hQ (show (⟨x, hPH hx⟩ : H) ∈ P.subgroupOf H from hx)
    exact ⟨_, this, rfl⟩

theorem card_conjSub_eq (g : G) (H : Subgroup G) : Nat.card (conjSub g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))

theorem card_le_of_isSylowTwoOf [Finite G] {S K H : Subgroup G} (hS : IsSylowTwoOf S K)
    (hHK : H ≤ K) (hH : IsPGroup 2 H) : Nat.card H ≤ Nat.card S := by
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hS hHK hH
  calc Nat.card H ≤ Nat.card (conjSub x S) := Subgroup.card_le_of_le hx
    _ = Nat.card S := card_conjSub_eq x S

end Basic

section Image

variable {Mb : Type u} [Group Mb] {M : Type v} [Group M] {M1 : Subgroup Mb} {b1 : M1 →* M}

@[expose] def timg (T : Subgroup Mb) (b1 : M1 →* M) : Subgroup M := (T.subgroupOf M1).map b1

theorem mem_timg {T : Subgroup Mb} {y : M} :
    y ∈ timg T b1 ↔ ∃ w : M1, (w : Mb) ∈ T ∧ b1 w = y := Subgroup.mem_map

theorem card_timg_inf_centralizer {T : Subgroup Mb} (hT : T ≤ M1) (hinj : Function.Injective b1)
    (w : M1) :
    Nat.card (timg T b1 ⊓ Subgroup.centralizer ({b1 w} : Set M) : Subgroup M) =
      Nat.card (T ⊓ Subgroup.centralizer ({(w : Mb)} : Set Mb) : Subgroup Mb) := by
  have h1 : timg T b1 ⊓ Subgroup.centralizer ({b1 w} : Set M) =
      ((T ⊓ Subgroup.centralizer ({(w : Mb)} : Set Mb)).subgroupOf M1).map b1 := by
    ext y
    constructor
    · rintro ⟨hy, hyc⟩
      obtain ⟨v, hv, rfl⟩ := mem_timg.mp hy
      refine Subgroup.mem_map.mpr ⟨v, ?_, rfl⟩
      have hcomm : b1 v * b1 w = b1 w * b1 v := Subgroup.mem_centralizer_singleton_iff.mp hyc
      rw [← map_mul, ← map_mul] at hcomm
      have hvw : v * w = w * v := hinj hcomm
      refine Subgroup.mem_subgroupOf.mpr ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg Subtype.val hvw
    · intro hy
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨hvT, hvc⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hv)
      refine ⟨mem_timg.mpr ⟨v, hvT, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hvw : (v : Mb) * (w : Mb) = (w : Mb) * (v : Mb) :=
        Subgroup.mem_centralizer_singleton_iff.mp hvc
      rw [← map_mul, ← map_mul]
      exact congrArg b1 (Subtype.ext hvw)
  rw [h1, Subgroup.card_map_of_injective hinj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hT)).toEquiv

end Image

section Sylow

variable {Mb : Type u} [Group Mb] [Finite Mb] {M : Type v} [Group M] [Finite M]
  {T M1 M2 : Subgroup Mb} {I : Finset Mb} {z t : Mb} {b1 : M1 →* M} {b2 : M2 →* M}

omit [Finite Mb] [Finite M] in
theorem orderOf_phi_of_mem₁ (C : F431Comp M1 M2 b1 b2) {i : Mb} (hi : i ∈ M1) :
    orderOf (amalgamMap b1 b2 i) = orderOf i := by
  rw [amalgamMap_of_mem₁ b1 b2 hi, orderOf_injective b1 C.inj₁]
  exact (Subgroup.orderOf_coe (⟨i, hi⟩ : M1)).symm

theorem loc442Q_sylow (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hnfI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    (ht : t ∈ I)
    (hSylt : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set Mb))
      (Subgroup.centralizer ({t} : Set Mb)))
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range) :
    IsSylowTwoOf (timg T b1 ⊓ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M))
      (Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M)) := by
  have hTt : t ∈ T := D.mem_T t ht
  have ht1 : t ∈ M1 := D.T_le₁ hTt
  have hSylP : IsSylowTwoOf (timg T b1) ⊤ := D.lemma_F433 C (Or.inl hb)
  have htφ : amalgamMap b1 b2 t = b1 ⟨t, ht1⟩ := amalgamMap_of_mem₁ b1 b2 ht1
  set tM : M := amalgamMap b1 b2 t with htM
  have hto : orderOf tM = 2 := by
    rw [htM, orderOf_phi_of_mem₁ C ht1]
    exact D.order_two t ht
  set P := timg T b1 with hP
  set R := P ⊓ Subgroup.centralizer ({tM} : Set M) with hR
  have htP : tM ∈ P := mem_timg.mpr ⟨⟨t, ht1⟩, hTt, htφ.symm⟩
  have htR : tM ∈ R := ⟨htP, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hRp : IsPGroup 2 R := hSylP.2.1.to_le inf_le_left
  obtain ⟨R', hR'syl, hRR'⟩ := exists_sylowTwo_ge (inf_le_right : R ≤ _) hRp
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hSylP (le_top : R' ≤ ⊤) hR'syl.2.1
  have htx : x⁻¹ * tM * x ∈ P := mem_conjSub.mp (hx (hRR' htR))
  obtain ⟨u, huT, hu⟩ := mem_timg.mp htx
  have hconj : IsConj tM (x⁻¹ * tM * x) := isConj_iff.mpr ⟨x⁻¹, by simp⟩
  have huo : orderOf (u : Mb) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective b1 C.inj₁ u, hu,
      ← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hconj, hto]
  have hφu : amalgamMap b1 b2 (u : Mb) = b1 u := amalgamMap_of_mem₁ b1 b2 u.2
  have hconjt : IsConj t (u : Mb) := by
    refine (D.lemma_F435 C hnfI hTt huT (D.order_two t ht) huo).mpr ?_
    rw [hφu, hu]
    exact hconj
  have hc1 : R' ≤ conjSub x (P ⊓ Subgroup.centralizer ({b1 u} : Set M)) := by
    intro y hy
    refine mem_conjSub.mpr (Subgroup.mem_inf.mpr ⟨mem_conjSub.mp (hx hy), ?_⟩)
    rw [Subgroup.mem_centralizer_singleton_iff, hu]
    have hyc : y * tM = tM * y := Subgroup.mem_centralizer_singleton_iff.mp (hR'syl.1 hy)
    calc x⁻¹ * y * x * (x⁻¹ * tM * x) = x⁻¹ * (y * tM) * x := by group
      _ = x⁻¹ * (tM * y) * x := by rw [hyc]
      _ = x⁻¹ * tM * x * (x⁻¹ * y * x) := by group
  have hc1' : Nat.card R' ≤ Nat.card (T ⊓ Subgroup.centralizer ({(u : Mb)} : Set Mb) :
      Subgroup Mb) := by
    rw [← card_timg_inf_centralizer D.T_le₁ C.inj₁ u]
    calc Nat.card R' ≤ Nat.card (conjSub x (P ⊓ Subgroup.centralizer ({b1 u} : Set M))) :=
          Subgroup.card_le_of_le hc1
      _ = _ := card_conjSub_eq x _
  obtain ⟨y, hy⟩ := isConj_iff.mp hconjt
  have hc3 : conjSub y⁻¹ (T ⊓ Subgroup.centralizer ({(u : Mb)} : Set Mb)) ≤
      Subgroup.centralizer ({t} : Set Mb) := by
    intro s hs
    obtain ⟨-, hsc⟩ := Subgroup.mem_inf.mp (mem_conjSub.mp hs)
    have hsc' := Subgroup.mem_centralizer_singleton_iff.mp hsc
    rw [← hy, inv_inv] at hsc'
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc s * t = y⁻¹ * ((y * s * y⁻¹) * (y * t * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * t * y⁻¹) * (y * s * y⁻¹)) * y := by rw [hsc']
      _ = t * s := by group
  have hc3' : Nat.card (T ⊓ Subgroup.centralizer ({(u : Mb)} : Set Mb) : Subgroup Mb) ≤
      Nat.card (T ⊓ Subgroup.centralizer ({t} : Set Mb) : Subgroup Mb) := by
    have hp : IsPGroup 2 (conjSub y⁻¹ (T ⊓ Subgroup.centralizer ({(u : Mb)} : Set Mb))) :=
      F7.isPGroup_conjSub (D.sylow.2.1.to_le inf_le_left)
    calc _ = Nat.card (conjSub y⁻¹ (T ⊓ Subgroup.centralizer ({(u : Mb)} : Set Mb))) :=
          (card_conjSub_eq _ _).symm
      _ ≤ _ := card_le_of_isSylowTwoOf hSylt hc3 hp
  have hcR : Nat.card R = Nat.card (T ⊓ Subgroup.centralizer ({t} : Set Mb) : Subgroup Mb) := by
    rw [hR, htφ]
    exact card_timg_inf_centralizer D.T_le₁ C.inj₁ ⟨t, ht1⟩
  have hle : Nat.card R' ≤ Nat.card R := by
    rw [hcR]
    exact hc1'.trans hc3'
  have hReq : R = R' := Subgroup.eq_of_le_of_card_ge hRR' hle
  rw [hReq]
  exact hR'syl

theorem loc442Q_exists_conj (D : F431LieK T M1 M2 I z) (C : F431Comp M1 M2 b1 b2)
    (hnfI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      ¬ IsConj (amalgamMap b1 b2 i) (amalgamMap b1 b2 j))
    (ht : t ∈ I)
    (hSylt : IsSylowTwoOf (T ⊓ Subgroup.centralizer ({t} : Set Mb))
      (Subgroup.centralizer ({t} : Set Mb)))
    (hb : Subgroup.centralizer ({amalgamMap b1 b2 z} : Set M) ≤ b1.range)
    {c : M} (hc : IsConj (amalgamMap b1 b2 z) c)
    (hct : c * amalgamMap b1 b2 t = amalgamMap b1 b2 t * c) :
    ∃ m ∈ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M),
      m⁻¹ * c * m ∈ timg T b1 ⊓ Subgroup.centralizer ({amalgamMap b1 b2 t} : Set M) := by
  have hco : orderOf c = 2 := by
    rw [← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hc,
      orderOf_phi_of_mem₁ C (D.T_le₁ (D.mem_T z D.z_mem))]
    exact D.order_two z D.z_mem
  exact exists_conj_mem_of_isSylowTwoOf_involution (loc442Q_sylow D C hnfI ht hSylt hb)
    (Subgroup.mem_centralizer_singleton_iff.mpr hct) hco

end Sylow

end CFSG.Quasithin.Loc442Q
