module

public import CFSG.Quasithin.Vol2.Ch12Sec5FinA
public import CFSG.Quasithin.H13.U3L14Grp
public import CFSG.Quasithin.Vol2.Ch12Sec5L2G

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S125

namespace S125Fin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_surj_of_quot {X V : Subgroup G} {Q : Type*} [Group Q]
    (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G)))
    (ψ : ↥(autOn X V) ⧸ CFSG.pCore 2 ↥(autOn X V) ≃* Q) :
    ∃ π : ↥X →* Q, Function.Surjective π ∧ IsPGroup 2 ↥π.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ₀ : ↥X →* ↥(autOn X V) := (A4.actionOn V X hXV).codRestrict (autOn X V)
    (fun x => (A4.mem_autOn_iff hXV).mpr ⟨x, rfl⟩)
  have hφ₀s : Function.Surjective φ₀ := by
    rintro ⟨a, ha⟩
    obtain ⟨x, rfl⟩ := (A4.mem_autOn_iff hXV).mp ha
    exact ⟨x, rfl⟩
  refine ⟨ψ.toMonoidHom.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥(autOn X V))).comp φ₀),
    ψ.surjective.comp ((QuotientGroup.mk'_surjective _).comp hφ₀s), ?_⟩
  intro x
  have hx : φ₀ x ∈ CFSG.pCore 2 ↥(autOn X V) := by
    have h1 := x.2
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(autOn X V))) ⟨_, hx⟩
  have h1 : A4.actionOn V X hXV ((x : ↥X) ^ 2 ^ k) = 1 := by
    have hk' : (φ₀ x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [map_pow]
    exact congrArg Subtype.val hk'
  have h2 : (((x : ↥X) ^ 2 ^ k : ↥X) : G) ∈ X ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨((x : ↥X) ^ 2 ^ k).2, (A4.actionOn_eq_one_iff hXV _).mp h1⟩
  obtain ⟨m, hm⟩ := hC ⟨_, h2⟩
  refine ⟨k + m, Subtype.ext (Subtype.ext ?_)⟩
  have h3 := congrArg (fun z : ↥(X ⊓ Subgroup.centralizer (V : Set G)) => (z : G)) hm
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3 ⊢
  rw [pow_add, pow_mul]
  exact h3

@[expose] def sl2Three : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨!![0, 1; 1, 1], by decide⟩

theorem commutator_mem_sl2 : ∀ a b : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = sl2Three ∨
      a * b * a⁻¹ * b⁻¹ = sl2Three * sl2Three := by
  decide

theorem card_sl2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem le_ker_snd_of_perfect
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))} (hP : ⁅P, P⁆ = P) :
    P ≤ (MonoidHom.snd _ _).ker := by
  set P₂ := P.map (MonoidHom.snd (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) with hP₂
  have hP₂p : ⁅P₂, P₂⁆ = P₂ := by rw [hP₂, ← Subgroup.map_commutator, hP]
  have hC : ⁅P₂, P₂⁆ ≤ Subgroup.zpowers sl2Three := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [commutatorElement_def]
    rcases commutator_mem_sl2 a b with h | h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
    · rw [h]; exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  have hab : ⁅Subgroup.zpowers sl2Three, Subgroup.zpowers sl2Three⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self sl2Three j i).eq
  have hP₂b : P₂ = ⊥ := by
    rw [← hP₂p, eq_bot_iff, ← hab]
    exact Subgroup.commutator_mono (hP₂p ▸ hC) (hP₂p ▸ hC)
  intro p hp
  have : p.2 ∈ P₂ := ⟨p, hp, rfl⟩
  rw [hP₂b, Subgroup.mem_bot] at this
  exact this

theorem le_sup_of_prod {M L₁ T : Subgroup G} {b : G}
    (π : ↥M →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ×
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hπ : Function.Surjective π) (hker : IsPGroup 2 ↥π.ker) (hL₁M : L₁ ≤ M)
    (hL₁n : M ≤ Subgroup.normalizer (L₁ : Set G)) (hperf : ⁅L₁, L₁⁆ = L₁)
    (hL₁2 : ¬ IsPGroup 2 ↥L₁) (hbM : b ∈ M) {k : ℕ} (hb3 : b ^ 3 ^ k = 1) (hb1 : b ≠ 1)
    (hbc : ∀ l ∈ L₁, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁) (hT : QuasithinUnique.IsSylowTwoOf T M) :
    M ≤ L₁ ⊔ Subgroup.zpowers b ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L' : Subgroup ↥M := L₁.subgroupOf M with hL'
  have hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hL₁M).mpr hL₁n
  have hL'map : L'.map M.subtype = L₁ := by
    rw [hL', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hL₁M]
  have hL'p : ⁅L', L'⁆ = L' := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, hL'map, hperf]
  set P := L'.map π with hP
  have hPn : P.Normal := hL'n.map π hπ
  have hPp : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hL'p]
  have hPsnd := le_ker_snd_of_perfect hPp
  have hP1 : P.map (MonoidHom.fst _ _) = ⊤ := by
    have hn : (P.map (MonoidHom.fst (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))).Normal :=
      hPn.map _ Prod.fst_surjective
    have hs := (isSimpleGroup_sl_zmod_two (m := 3) (by norm_num)).1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (P.map (MonoidHom.fst (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))) with h | h
    · exfalso
      apply hL₁2
      have hPb : P = ⊥ := by
        rw [eq_bot_iff]
        intro p hp
        have h1 : p.1 ∈ P.map (MonoidHom.fst _ _) := ⟨p, hp, rfl⟩
        rw [h, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.mpr (Prod.ext h1 (hPsnd hp))
      have hL'k : L' ≤ π.ker := by
        intro x hx
        have : π x ∈ P := ⟨x, hx, rfl⟩
        rw [hPb, Subgroup.mem_bot] at this
        exact this
      intro l
      obtain ⟨j, hj⟩ := hker ⟨⟨l, hL₁M l.2⟩, hL'k (show ⟨(l : G), hL₁M l.2⟩ ∈ L' from l.2)⟩
      refine ⟨j, Subtype.ext ?_⟩
      have := congrArg (fun z : ↥π.ker => ((z : ↥M) : G)) hj
      simpa using this
    · exact h
  have hPx : ∀ x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), ∃ l ∈ L', π l = (x, 1) := by
    intro x
    obtain ⟨p, hp, hpx⟩ : x ∈ P.map (MonoidHom.fst _ _) := hP1 ▸ Subgroup.mem_top x
    obtain ⟨l, hl, rfl⟩ := hp
    exact ⟨l, hl, Prod.ext hpx (hPsnd ⟨l, hl, rfl⟩)⟩
  set O : Subgroup ↥M := (pCoreOf 2 L₁).subgroupOf M with hO
  have hOL : pCoreOf 2 L₁ ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 L₁).trans hL₁M
  have hOn : O.Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOL).mpr ?_
    have hchar : (CFSG.Open.pCore 2 ↥L₁).Characteristic := by
      infer_instance
    exact hL₁n.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.Open.pCore 2 ↥L₁))
  have hO2 : IsPGroup 2 ↥O :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁).of_equiv
      (Subgroup.subgroupOfEquivOfLe hOL).symm
  have hOπ : O.map π = ⊥ :=
    S125Pb.noO2_prod S125Pb.noO2_SL3 S125Pb.noO2_SL2 _ (hOn.map π hπ) (hO2.map π)
  set b' : ↥M := ⟨b, hbM⟩ with hb'
  have hcomm : ∀ x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      π b' * (x, 1) = (x, 1) * π b' := by
    intro x
    obtain ⟨l, hl, hlx⟩ := hPx x
    have hw : b' * l * b'⁻¹ * l⁻¹ ∈ O := by
      rw [hO, Subgroup.mem_subgroupOf]
      simpa using hbc (l : G) hl
    have h1 : π (b' * l * b'⁻¹ * l⁻¹) = 1 := by
      have : π (b' * l * b'⁻¹ * l⁻¹) ∈ O.map π := ⟨_, hw, rfl⟩
      rwa [hOπ, Subgroup.mem_bot] at this
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hlx] at h1
    rw [← mul_inv_eq_one, mul_inv_rev, ← mul_assoc]
    exact h1
  have hb₁ : (π b').1 = 1 := by
    have hZ := center_eq_bot_of_mulEquiv_sl (by norm_num)
      (MulEquiv.refl (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    have hc : (π b').1 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg Prod.fst (hcomm x)
      simpa using this.symm
    rwa [hZ, Subgroup.mem_bot] at hc
  have hπb : π b' ≠ 1 := by
    intro h
    obtain ⟨j, hj⟩ := hker ⟨b', h⟩
    have hj' : b ^ 2 ^ j = 1 := by
      have := congrArg (fun z : ↥π.ker => ((z : ↥M) : G)) hj
      simpa using this
    have h1 : orderOf b ∣ Nat.gcd (2 ^ j) (3 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hb3)
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow _ _ (by norm_num)), Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    exact hb1 h1
  set y := (π b').2 with hy
  have hy1 : y ≠ 1 := fun h => hπb (Prod.ext hb₁ h)
  have hy3 : y ^ 3 ^ k = 1 := by
    have h1 : (π b') ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have : b' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hb3)
      rw [this, map_one]
    have := congrArg Prod.snd h1
    simpa [hy] using this
  have hyo : orderOf y = 3 := by
    have h1 : orderOf y ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hy3
    have h2 : orderOf y ∣ 6 := card_sl2 ▸ orderOf_dvd_natCard y
    obtain ⟨i, hi, hie⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    have hy1' : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
    rcases i with _ | _ | i
    · exact absurd (by simpa using hie) hy1'
    · simpa using hie
    · exfalso
      rw [hie] at h2
      have : 3 ^ (i + 2) ≤ 6 := Nat.le_of_dvd (by norm_num) h2
      have : 9 ≤ 3 ^ (i + 2) := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (i + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  set Y : Subgroup ↥M := (L₁ ⊔ Subgroup.zpowers b ⊔ T).subgroupOf M with hY
  have hTY : T.subgroupOf M ≤ Y := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx))
  have hYodd : ¬ 2 ∣ Y.index := fun h => hT.2.2 (h.trans (Subgroup.index_dvd_of_le hTY))
  have hYimg : (Subgroup.zpowers y).comap (MonoidHom.snd _ _) ≤ Y.map π := by
    intro p hp
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (show p.2 ∈ Subgroup.zpowers y from hp)
    obtain ⟨l, hl, hlx⟩ := hPx p.1
    refine ⟨l * b' ^ i, Y.mul_mem ?_ (Y.zpow_mem ?_ i), ?_⟩
    · rw [hY, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hl)
    · rw [hY, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
    · rw [map_mul, map_zpow, hlx]
      apply Prod.ext
      · simp [hb₁]
      · simp [← hy, hi]
  have hidx2 : ((Subgroup.zpowers y).comap
      (MonoidHom.snd (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))).index = 2 := by
    rw [Subgroup.index_comap_of_surjective _ Prod.snd_surjective]
    have h := Subgroup.index_mul_card (Subgroup.zpowers y)
    rw [Nat.card_zpowers, hyo, card_sl2] at h
    omega
  have hidx : (Y.map π).index = 1 := by
    have h1 := Subgroup.index_dvd_of_le hYimg
    rw [hidx2] at h1
    have h2 := Subgroup.index_map_dvd Y hπ
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hYodd
  have hYtop : Y.map π = ⊤ := Subgroup.index_eq_one.mp hidx
  have hkerT : π.ker ≤ Y := by
    have hT' : IsPGroup 2 ↥(T.subgroupOf M) :=
      hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
    let S : Sylow 2 ↥M := hT'.toSylow hT.2.2
    exact (hker.le_sylow_of_normal S).trans hTY
  have hYeq : Y = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨y', hy', hyy⟩ : π m ∈ Y.map π := hYtop ▸ Subgroup.mem_top _
    have h1 : y'⁻¹ * m ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyy, inv_mul_cancel]
    have h2 := Y.mul_mem hy' (hkerT h1)
    simpa using h2
  exact Subgroup.subgroupOf_eq_top.mp hYeq

theorem mi_le_sup (h1222 : Stmt12_2_2) {T L V : Subgroup G} {F : Frame125 T L V}
    (hH : Hyp125 G T L V) (h2 : Concl12_5_2 T L V F)
    (hL₁c : quasithinIsCComponent (li L F.V1) (Subgroup.normalizer (F.V1 : Set G)))
    (hG₁N : Subgroup.normalizer (F.V1 : Set G) ≤ Subgroup.normalizer (li L F.V1 : Set G))
    {b : G} (hbM : b ∈ mi T L F.V1) {k : ℕ} (hb3 : b ^ 3 ^ k = 1) (hb1 : b ≠ 1)
    (hbc : ∀ l ∈ li L F.V1, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 (li L F.V1)) :
    mi T L F.V1 ≤ li L F.V1 ⊔ Subgroup.zpowers b ⊔ T := by
  have hf := S125Ex.Facts125.of h1222 hH
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hf.normalizes hf.T_le
  have hMV : mi T L F.V1 ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hLTV
  have hC : IsPGroup 2 ↥(mi T L F.V1 ⊓ Subgroup.centralizer (V : Set G)) :=
    (S125Tr2.isPGroup_centralizer hH hf).to_le (inf_le_inf_right _ inf_le_left)
  obtain ⟨ψ⟩ := h2.1.2.1
  obtain ⟨π, hπ, hker⟩ := exists_surj_of_quot hMV hC ψ
  have hTV₁ : T ≤ Subgroup.normalizer (F.V1 : Set G) := (S125L2G.T_le_V F hf.T_le).1
  have hTM : T ≤ mi T L F.V1 := le_inf le_sup_right hTV₁
  have hL₁M : li L F.V1 ≤ mi T L F.V1 :=
    (Subgroup.map_subtype_le _).trans (inf_le_inf_right _ le_sup_left)
  have hT : QuasithinUnique.IsSylowTwoOf T (mi T L F.V1) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hH.hyp.sylow hTM
  exact le_sup_of_prod π hπ hker hL₁M (inf_le_right.trans hG₁N) hL₁c.2.1
    (U3.not_isPGroup_of_perfect hL₁c.2.1 hL₁c.1) hbM hb3 hb1 hbc hT

end S125Fin

end CFSG.Quasithin.H13
