module

public import CFSG.Quasithin.EmptyFaithful.S143KL
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

open A6Model

theorem card_map_mul_card_inf_ker_of_hom {G H : Type*} [Group G] [Group H] (K : Subgroup G)
    (f : G →* H) : Nat.card ↥(K.map f) * Nat.card ↥(K ⊓ f.ker) = Nat.card K := by
  have h1 : f.ker.relIndex K = Nat.card (K.map f) := Subgroup.relIndex_ker K f
  have h2 := Subgroup.relIndex_mul_card f.ker K
  rw [h1, inf_comm] at h2
  exact h2

theorem card_alt6 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

section CardRU

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

theorem Counter.card_rOf_sup_uOfL22 : Nat.card ↥(rOf T M ⊔ uOfL22 T M) = 128 := by
  have hUI : ∀ u ∈ uOfL22 T M, u ∈ iTwo T M := fun u hu => le_conjClosure _ _ hu
  have hURN : uOfL22 T M ≤ Subgroup.normalizer (rOf T M : Set G) := fun u hu =>
    le_normalizer_pCoreOf 2 (iTwo T M) (hUI u hu)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hURN
  have hinf : rOf T M ⊓ uOfL22 T M = Hyp1281Two.wOfU T M := by
    apply le_antisymm
    · intro w hw
      have : w ∈ rOf T M ⊓ qOf T := ⟨hw.1, uOfL22_le_qOf c hw.2⟩
      rwa [rOf_inf_qOf c] at this
    · intro w hw
      exact ⟨c.mem_rOf_of_mem_wOfU hw, hw.1⟩
  have hW : Nat.card ↥(Hyp1281Two.wOfU T M) = 16 := card_wOf c
  rw [hinf, hW, card_rOf c, c.c15.q8sq.1] at hprod
  omega

end CardRU

section CapRU

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {c : Counter T M g}
  {r : G} {hrW : r ∈ Hyp1281Two.wOfU T M} {hrV : r ∉ VZ T M} {hr2 : r * r = 1}
  {x z a r1 : G} (hS : Setup c hrW hrV hr2 x z a r1) {t : G} (htT : t ∈ T)
  (htRQ : t ∉ rOf T M ⊔ qOf T)
  {y : G} {cm : Mat4} (hM : KModel hS cm y)

include hS htT htRQ hM

theorem Setup.inf_centralizer_le_Ac {p : G} (hp : p ∈ rOf T M ⊔ uOfL22 T M)
    (hC : p ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G)) : p ∈ c.Ac hrW hrV hr2 := by
  have hB := hS.basis
  have hUI : ∀ u ∈ uOfL22 T M, u ∈ iTwo T M := fun u hu => le_conjClosure _ _ hu
  have hUN : ∀ u ∈ uOfL22 T M, u ∈ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    fun u hu => c.iTwo_le_normalizer_Ac hrW hrV hr2 (hUI u hu)
  have hRN := c.rOf_le_normalizer_Ac hrW hrV hr2
  have hURN : uOfL22 T M ≤ Subgroup.normalizer (rOf T M : Set G) := fun u hu =>
    le_normalizer_pCoreOf 2 (iTwo T M) (hUI u hu)
  obtain ⟨ρ', hρ', u, hu, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hURN).1 hp
  have hAC : ∀ w ∈ c.Ac hrW hrV hr2, w ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) :=
    fun w hw => Subgroup.mem_centralizer_iff.mpr fun a' ha' => hB.comm a' ha' w hw
  have hRC := c.centralizer_inf_rOf_Ac hrW hrV hr2 htT htRQ
  have hZA : ∀ w ∈ quasithinOmegaOneCenter T, w ∈ c.Ac hrW hrV hr2 := fun w hw =>
    c.VZ_le_Ac hrW hrV hr2 (Hyp1281Two.omegaOneCenter_le_VZ T M hw)
  have h1 : mm (cmat z a r r1 u) (cmat z a r r1 ρ') = I4 := by
    rw [← hB.cmat_mul (hRN hρ') (hUN u hu)]
    exact (hB.cmat_eq_one_iff_mem_centralizer
      (Subgroup.mul_mem _ (hRN hρ') (hUN u hu))).mpr hC
  have hsq : mm (cmat z a r r1 u) (cmat z a r r1 u) = I4 := by
    rw [← hB.cmat_mul (hUN u hu) (hUN u hu)]
    exact (hB.cmat_eq_one_iff_mem_centralizer (Subgroup.mul_mem _ (hUN u hu) (hUN u hu))).mpr
      (hAC _ (hZA _ (c.mul_self_mem_Z hu)))
  have h2 : cmat z a r r1 ρ' = cmat z a r r1 u := by
    calc cmat z a r r1 ρ' = mm I4 (cmat z a r r1 ρ') := (I4_mm _).symm
      _ = mm (mm (cmat z a r r1 u) (cmat z a r r1 u)) (cmat z a r r1 ρ') := by rw [hsq]
      _ = mm (cmat z a r r1 u) (mm (cmat z a r r1 u) (cmat z a r r1 ρ')) := mm_assoc _ _ _
      _ = cmat z a r r1 u := by rw [h1, mm_I4]
  by_cases hI : cmat z a r r1 u = I4
  ·
    have hu' : u ∈ c.Ac hrW hrV hr2 :=
      c.centralizer_inf_uOfL22_le_Ac hrW hrV hr2 htT htRQ hu
        ((hB.cmat_eq_one_iff_mem_centralizer (hUN u hu)).mp hI)
    have hρ'A : ρ' ∈ c.Ac hrW hrV hr2 := by
      have : ρ' ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ⊓ rOf T M :=
        ⟨(hB.cmat_eq_one_iff_mem_centralizer (hRN hρ')).mp (h2.trans hI), hρ'⟩
      rwa [hRC] at this
    exact (c.Ac hrW hrV hr2).mul_mem hρ'A hu'
  ·
    obtain ⟨w, hwW, hwA, hwne⟩ := hS.exists_w htT htRQ
    have hwR : w ∈ rOf T M := c.mem_rOf_of_mem_wOfU hwW
    have hwU : w ∈ uOfL22 T M := hwW.1
    have hρ'ne : cmat z a r r1 ρ' ≠ I4 := fun h => hI (h2.symm.trans h)
    have hρw : cmat z a r r1 ρ' = cmat z a r r1 w :=
      hM.inter ρ' hρ' u hu w hwR w hwU h2 hρ'ne rfl hwne
    have huw : cmat z a r r1 u = cmat z a r r1 w := h2.symm.trans hρw
    have hwN := hRN hwR
    have ha₁ : w⁻¹ * ρ' ∈ c.Ac hrW hrV hr2 := by
      have h3 := (hB.cmat_eq_iff_mem_centralizer hwN (hRN hρ')).mp hρw.symm
      have : w⁻¹ * ρ' ∈ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ⊓ rOf T M :=
        ⟨h3, (rOf T M).mul_mem ((rOf T M).inv_mem hwR) hρ'⟩
      rwa [hRC] at this
    have ha₂ : w⁻¹ * u ∈ c.Ac hrW hrV hr2 := by
      have h3 := (hB.cmat_eq_iff_mem_centralizer hwN (hUN u hu)).mp huw.symm
      exact c.centralizer_inf_uOfL22_le_Ac hrW hrV hr2 htT htRQ
        ((uOfL22 T M).mul_mem ((uOfL22 T M).inv_mem hwU) hu) h3
    have hww : w * w ∈ c.Ac hrW hrV hr2 := hZA _ (c.mul_self_mem_Z hwU)
    have hconj : w⁻¹ * (w⁻¹ * ρ') * w⁻¹⁻¹ ∈ c.Ac hrW hrV hr2 :=
      conj_mem_of_mem_normalizer ((Subgroup.normalizer _).inv_mem hwN) ha₁
    have e : ρ' * u = (w * w) * (w⁻¹ * (w⁻¹ * ρ') * w⁻¹⁻¹) * (w⁻¹ * u) := by group
    rw [e]
    exact (c.Ac hrW hrV hr2).mul_mem ((c.Ac hrW hrV hr2).mul_mem hww hconj) ha₂

theorem Setup.kOf_inf_centralizer_le :
    kOf T M (c.Ac hrW hrV hr2) ⊓ Subgroup.centralizer (c.Ac hrW hrV hr2 : Set G) ≤
      c.Ac hrW hrV hr2 := by
  have hB := hS.basis
  have hKN : kOf T M (c.Ac hrW hrV hr2) ≤ Subgroup.normalizer (c.Ac hrW hrV hr2 : Set G) :=
    c.kOf_le_normalizer_Ac hrW hrV hr2
  have hK := hM.K_le
  have hcomm := hS.K_le_commSub htT htRQ hM
  have hRUK := c.rOf_sup_uOfL22_le_kOf hrW hrV hr2
  have hAR : c.Ac hrW hrV hr2 ≤ rOf T M := c.Ac_le_rOf hrW hrV hr2
  have hAP0 : c.Ac hrW hrV hr2 ≤ rOf T M ⊔ uOfL22 T M := hAR.trans le_sup_left
  have hAK : c.Ac hrW hrV hr2 ≤ kOf T M (c.Ac hrW hrV hr2) := hAP0.trans hRUK
  have hΓ2 := c.isPGroup_centralizer_Ac hrW hrV hr2
  have hsurj := homK_surjective hB hM.inj hK hM.x_K hM.y_K hM.count
  set K := kOf T M (c.Ac hrW hrV hr2) with hKdef
  set A := c.Ac hrW hrV hr2 with hAdef
  set q := homK hB hM.inj hK with hq
  set Ck : Subgroup ↥K := q.ker with hCkdef
  have hCk : ∀ k : ↥K, k ∈ Ck ↔ (k : G) ∈ Subgroup.centralizer (A : Set G) := fun k =>
    (homK_eq_one_iff hB hM.inj hK k).trans (hB.cmat_eq_one_iff_mem_centralizer (hKN k.2))
  set AK : Subgroup ↥K := A.subgroupOf K with hAKdef
  have hAKnormal : AK.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKN
  have hAKC : AK ≤ Ck := fun k hk => (hCk k).mpr (Subgroup.mem_centralizer_iff.mpr fun a' ha' =>
    hB.comm a' ha' k hk)
  set P0 : Subgroup G := rOf T M ⊔ uOfL22 T M with hP0
  set P0K : Subgroup ↥K := P0.subgroupOf K with hP0Kdef
  have hAKP : AK ≤ P0K := fun k hk => hAP0 hk
  set π : ↥K →* ↥K ⧸ AK := QuotientGroup.mk' AK with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective AK
  have hπker : π.ker = AK := QuotientGroup.ker_mk' AK
  set Nbar : Subgroup (↥K ⧸ AK) := Ck.map π with hNbar
  set Pbar0 : Subgroup (↥K ⧸ AK) := P0K.map π with hPbar0
  have hcentral : ∀ n ∈ Nbar, ∀ kb : ↥K ⧸ AK, n * kb = kb * n := by
    rintro n ⟨c', hc', rfl⟩ kb
    obtain ⟨k, rfl⟩ := hπsurj kb
    rw [← map_mul, ← map_mul]
    apply (QuotientGroup.eq).mpr
    have hc'Γ : (c' : G) ∈ Subgroup.centralizer (A : Set G) := (hCk c').mp hc'
    have h1 := (hcomm ((kOf T M A).inv_mem k.2)).2 ((c' : G)⁻¹) (Subgroup.inv_mem _ hc'Γ)
    show ((c' * k)⁻¹ * (k * c') : ↥K) ∈ AK
    show (((c' : G) * (k : G))⁻¹ * ((k : G) * (c' : G))) ∈ A
    have e : ((c' : G) * (k : G))⁻¹ * ((k : G) * (c' : G)) =
        (k : G)⁻¹ * (c' : G)⁻¹ * (k : G)⁻¹⁻¹ * (c' : G)⁻¹⁻¹ := by group
    rw [e]; exact h1
  have hNnormal : Nbar.Normal := Subgroup.Normal.map inferInstance π hπsurj
  have hNcomm : IsMulCommutative Nbar :=
    ⟨⟨fun a b => Subtype.ext (hcentral a a.2 b)⟩⟩
  have hN2 : IsPGroup 2 Nbar := by
    rintro ⟨n, c', hc', rfl⟩
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hΓ2) ⟨(c' : G), (hCk c').mp hc'⟩
    refine ⟨m, Subtype.ext ?_⟩
    have h1 : (c' : G) ^ 2 ^ m = 1 := by
      have := pow_orderOf_eq_one
        (⟨(c' : G), (hCk c').mp hc'⟩ : ↥(Subgroup.centralizer (A : Set G)))
      rw [hm] at this
      exact congrArg Subtype.val this
    have h2 : c' ^ 2 ^ m = 1 := Subtype.ext h1
    show (π c') ^ 2 ^ m = 1
    rw [← map_pow, h2, map_one]
  have hNP : Nbar ⊓ Pbar0 = ⊥ := by
    rw [eq_bot_iff]
    rintro n ⟨⟨c', hc', hcn⟩, ⟨p, hp, hpn⟩⟩
    have hcp : (c'⁻¹ * p : ↥K) ∈ AK := by
      rw [← hπker]
      show π (c'⁻¹ * p) = 1
      rw [map_mul, map_inv, hcn, hpn, inv_mul_cancel]
    have hpC : p ∈ Ck := by
      have := Ck.mul_mem hc' (hAKC hcp)
      simpa using this
    have hpA : (p : G) ∈ A :=
      hS.inf_centralizer_le_Ac htT htRQ hM hp ((hCk p).mp hpC)
    rw [Subgroup.mem_bot, ← hpn]
    exact (QuotientGroup.eq_one_iff p).mpr hpA
  have hAcard : Nat.card AK = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
    exact c.card_Ac hrW hrV hr2
  have hCardK : Nat.card ↥K = 360 * Nat.card Ck := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Ck,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hsurj).toEquiv, card_alt6]
  have hCardKbar : Nat.card (↥K ⧸ AK) * 16 = Nat.card ↥K := by
    have := Subgroup.index_mul_card AK
    rw [hAcard] at this
    exact this
  have hCardN : Nat.card Nbar * 16 = Nat.card Ck := by
    have h := card_map_mul_card_inf_ker_of_hom Ck π
    rw [hπker, inf_eq_right.mpr hAKC, hAcard] at h
    exact h
  have hCardP0 : Nat.card Pbar0 * 16 = 128 := by
    have h := card_map_mul_card_inf_ker_of_hom P0K π
    rw [hπker, inf_eq_right.mpr hAKP, hAcard] at h
    rw [h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRUK).toEquiv]
    exact c.card_rOf_sup_uOfL22
  have hNnorm : Pbar0 ≤ Subgroup.normalizer (Nbar : Set (↥K ⧸ AK)) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hNPcard : Nat.card ↥(Nbar ⊔ Pbar0) = Nat.card Nbar * Nat.card Pbar0 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hNnorm
    rw [hNP, Subgroup.card_bot, mul_one] at h
    exact h
  have hn : 0 < Nat.card Nbar := Nat.card_pos
  have hP0c : Nat.card Pbar0 = 8 := by omega
  have hKbarc : Nat.card (↥K ⧸ AK) = 360 * Nat.card Nbar := by omega
  have hPcard : Nat.card ↥(Nbar ⊔ Pbar0) = 8 * Nat.card Nbar := by
    rw [hNPcard, hP0c]; ring
  have hindex45 : (Nbar ⊔ Pbar0).index = 45 := by
    have h := Subgroup.card_mul_index (Nbar ⊔ Pbar0)
    rw [hPcard, hKbarc] at h
    have h' : (8 * (Nbar ⊔ Pbar0).index) * Nat.card Nbar = 45 * 8 * Nat.card Nbar := by
      nlinarith [h]
    have := Nat.eq_of_mul_eq_mul_right hn h'
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 ↥(Nbar ⊔ Pbar0) := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    refine IsPGroup.of_card (n := k + 3) ?_
    rw [hPcard, hk]; ring
  have hindex : ¬ 2 ∣ (Nbar ⊔ Pbar0).index := by rw [hindex45]; decide
  let P : Sylow 2 (↥K ⧸ AK) := hP2.toSylow hindex
  have hPeq : (P : Subgroup (↥K ⧸ AK)) = Nbar ⊔ Pbar0 := rfl
  have hNP' : Nbar ≤ (P : Subgroup (↥K ⧸ AK)) := by rw [hPeq]; exact le_sup_left
  have := hNnormal
  have := hNcomm
  obtain ⟨D, hND, hNDsup⟩ := SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement
    Nat.prime_two hN2 P hNP' hNP hPeq.symm
  have hDN : D ≤ Subgroup.normalizer (Nbar : Set (↥K ⧸ AK)) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hpow : ∀ x ∈ K, ∃ m : ℕ, x ^ 2 ^ m ∈ (D.comap π).map K.subtype := by
    intro x hx
    have hk : π ⟨x, hx⟩ ∈ Nbar ⊔ D := by rw [hNDsup]; exact Subgroup.mem_top _
    obtain ⟨n, hn', d, hd, hnd⟩ := (Lin2.mem_sup_iff_of_le_normalizer hDN).1 hk
    obtain ⟨m, hm⟩ := hN2 ⟨n, hn'⟩
    have hnm : n ^ 2 ^ m = 1 := congrArg Subtype.val hm
    refine ⟨m, ⟨⟨x, hx⟩ ^ 2 ^ m, ?_, rfl⟩⟩
    show π (⟨x, hx⟩ ^ 2 ^ m) ∈ D
    rw [map_pow, hnd, (Commute.mul_pow (hcentral n hn' d) (2 ^ m)), hnm, one_mul]
    exact Subgroup.pow_mem _ hd _
  have hKle : K ≤ (D.comap π).map K.subtype := by
    have := oTwoUpper_le_of_pow_mem hpow
    rwa [oTwoUpper_kOf] at this
  have hDtop : D = ⊤ := by
    rw [eq_top_iff]
    intro d' _
    obtain ⟨k, rfl⟩ := hπsurj d'
    obtain ⟨k', hk', hk'k⟩ := hKle k.2
    have : k' = k := Subtype.ext hk'k
    rw [← this]
    exact hk'
  have hNbot : Nbar = ⊥ := by
    rw [← inf_top_eq Nbar, ← hDtop]; exact hND
  intro k hk
  have hkΓ : k ∈ Subgroup.centralizer (A : Set G) := hk.2
  have hkC : (⟨k, hk.1⟩ : ↥K) ∈ Ck := (hCk _).mpr hkΓ
  have hπk : π ⟨k, hk.1⟩ ∈ Nbar := ⟨_, hkC, rfl⟩
  rw [hNbot, Subgroup.mem_bot] at hπk
  exact (QuotientGroup.eq_one_iff (N := AK) (⟨k, hk.1⟩ : ↥K)).mp hπk

end CapRU

end S143

end CFSG.Quasithin
