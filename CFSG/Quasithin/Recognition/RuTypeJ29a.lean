module

public import CFSG.Quasithin.Recognition.RuTypeJ27l

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

noncomputable abbrev Cen (x : G) : Subgroup G := Subgroup.centralizer ({x} : Set G)

theorem mem_Cen {x g : G} : g ∈ Cen x ↔ g * x = x * g := Subgroup.mem_centralizer_singleton_iff

namespace RuDataM

variable (M : RuDataM G) [Finite G]

theorem exists_cel_conj_V {v w : G} (hv : v ∈ ruV M.L) (hw : w ∈ ruV M.L) (hv1 : v ≠ 1)
    (hw1 : w ≠ 1) : ∃ k : ℕ, (M.cel : G) ^ k * v * ((M.cel : G) ^ k)⁻¹ = w := by
  have hne : ∀ (x : G) (hx : x ∈ ruV M.L), x ≠ 1 → Multiplicative.toAdd (M.ψV ⟨x, hx⟩) ≠ 0 := by
    intro x hx hx1 h0
    have : M.ψV ⟨x, hx⟩ = 1 := Multiplicative.toAdd.injective h0
    have h1 := congrArg Subtype.val (M.ψV.injective (this.trans (map_one M.ψV).symm))
    exact hx1 h1
  obtain ⟨k, hk⟩ := SL3.c0_trans_vec _ _ ⟨hne v hv hv1, hne w hw hw1⟩
  refine ⟨k.val, ?_⟩
  have hc : (M.cel : G) ^ k.val * v * ((M.cel : G) ^ k.val)⁻¹ ∈ ruV M.L :=
    M.toRuData.conj_mem_V (M.cel ^ k.val).2 hv
  have e := M.ψV_conj_cel_pow k.val ⟨v, hv⟩ hc
  rw [← hk] at e
  have := M.ψV.injective (Multiplicative.toAdd.injective e)
  exact congrArg Subtype.val this

theorem cel_pow_conj_S1 (k : ℕ) {y : G} (hy : y ∈ M.S1) :
    (M.cel : G) ^ k * y * ((M.cel : G) ^ k)⁻¹ ∈ M.S1 := by
  induction k with
  | zero => simpa using hy
  | succ k ih =>
    have h := M.cel_conj_S1 ih
    have e : (M.cel : G) ^ (k + 1) * y * ((M.cel : G) ^ (k + 1))⁻¹ =
        (M.cel : G) * ((M.cel : G) ^ k * y * ((M.cel : G) ^ k)⁻¹) * (M.cel : G)⁻¹ := by
      rw [pow_succ']; group
    rw [e]
    exact h

theorem exists_sq_eq_V {v : G} (hv : v ∈ ruV M.L) : ∃ x ∈ M.S1, x ^ 2 = v := by
  by_cases hv1 : v = 1
  · exact ⟨1, one_mem _, by rw [hv1, one_pow]⟩
  have hex : ∃ y ∈ M.S1, y ∉ ruV M.L := by
    by_contra hno
    push Not at hno
    apply M.S1_not_comm
    intro a ha b hb
    exact (M.V_comm_S (hno a ha) (M.S1_le_S hb)).symm
  obtain ⟨y, hy, hyV⟩ := hex
  have hy2 : y ^ 2 ∈ ruV M.L := M.sq_mem_V (M.S1_le_S hy)
  have hy21 : y ^ 2 ≠ 1 := M.sq_ne_one_of_S1 hy hyV
  obtain ⟨k, hk⟩ := M.exists_cel_conj_V hy2 hv hy21 hv1
  refine ⟨(M.cel : G) ^ k * y * ((M.cel : G) ^ k)⁻¹, M.cel_pow_conj_S1 k hy, ?_⟩
  rw [conj_pow, hk]

theorem mem_L_of_normalizes_S3 {n : G} (hn : ∀ x ∈ M.S3, n * x * n⁻¹ ∈ M.S3) : n ∈ M.L := by
  rw [M.one.eq_normalizer]
  refine mem_normalizer_of_conj_mem fun v hv => ?_
  obtain ⟨x, hx, rfl⟩ := M.exists_sq_eq_V hv
  rw [← conj_pow]
  exact M.sq_mem_V (M.S3_le_S (hn x (M.S1_le_S3 hx)))

theorem comm_S0_of_mem_CL {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {n : G} (hnL : n ∈ M.L)
    (hns : n * s = s * n) {s' : G} (hs' : s' ∈ M.S0) : n * s' = s' * n := by
  have hn : n ∈ M.L ⊓ Subgroup.centralizer ({s} : Set G) :=
    ⟨hnL, Subgroup.mem_centralizer_singleton_iff.mpr hns⟩
  rw [(M.lemma_J23_3 hs hs1).1, M.commutator_eq_S1 hs hs1] at hn
  have hle : M.S0 ⊔ M.S1 ⊔ M.B7 ≤ Subgroup.centralizer ({s'} : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (M.S0_elem.1.is_comm.comm ⟨x, hx⟩ ⟨s', hs'⟩ |> congrArg Subtype.val)
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (M.comm_S0_S1 hs' hx).symm
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact ((M.mem_S0.mp hs').2)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hn)

theorem S3_le_H : M.S3 ≤ ruH M.T := fun _ hx => M.toRuData.T_le_H (M.toRuData.S_le_T (M.S3_le_S hx))

theorem centralizer_H_eq_S3
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ruH M.T ⊓ Cen s = M.S3 := by
  rw [M.centralizer_H_eq hs hs1, M.centralizer_eq_S3 hs hs1]

theorem S3_le_Cen
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) : M.S3 ≤ Cen s := by
  rw [← M.centralizer_H_eq_S3 hs hs1]
  exact inf_le_right

theorem comm_S3_of_sq {y : G} (hy : y ∈ M.S3) (hy2 : y ^ 2 = 1) {t : G} (ht : t ∈ M.S3) :
    y * t = t * y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := M.exists_S0_S1 hy
  have hab : a * b = b * a := M.comm_S0_S1 ha hb
  have ha2 : a ^ 2 = 1 := M.S0_elem.2 a ha
  have hb2 : b ^ 2 = 1 := by
    have h : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by rw [(Commute.mul_pow hab 2)]
    rw [hy2, ha2, one_mul] at h
    exact h.symm
  have hbV : b ∈ ruV M.L := M.mem_V_of_S1_sq hb hb2
  have h1 : a * t = t * a := M.comm_S0_S3 ha ht
  have h2 : b * t = t * b := (M.V_comm_S hbV (M.S3_le_S ht)).symm
  calc a * b * t = a * (t * b) := by rw [mul_assoc, h2]
    _ = t * (a * b) := by rw [← mul_assoc, h1, mul_assoc]

theorem conj_S0_eq
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {s' : G} (hs' : s' ∈ M.S0) {g : G}
    (hg : g ∈ Cen s) (hgs : g * s' * g⁻¹ ∈ M.S3) : g * s' * g⁻¹ = s' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set y := g * s' * g⁻¹ with hydef
  have hy2 : y ^ 2 = 1 := by rw [hydef, conj_pow, M.S0_elem.2 _ hs']; group
  set Y := Cen s ⊓ Cen y with hYdef
  have hS3Y : M.S3 ≤ Y := fun t ht =>
    Subgroup.mem_inf.mpr ⟨M.S3_le_Cen hs hs1 ht, mem_Cen.mpr (M.comm_S3_of_sq hgs hy2 ht).symm⟩
  set S3g := M.S3.map (MulAut.conj g).toMonoidHom
  have hS3gY : S3g ≤ Y := by
    rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg (M.S3_le_Cen hs hs1 ht)) (inv_mem hg),
      mem_Cen.mpr ?_⟩
    have hts : t * s' = s' * t := (M.comm_S0_S3 hs' ht).symm
    rw [hydef]
    calc g * t * g⁻¹ * (g * s' * g⁻¹) = g * (t * s') * g⁻¹ := by group
      _ = g * (s' * t) * g⁻¹ := by rw [hts]
      _ = g * s' * g⁻¹ * (g * t * g⁻¹) := by group
  have hY9 : ¬ 2 ^ 9 ∣ Nat.card Y := fun h =>
    M.not_dvd_card_centralizer hs hs1 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hfac : (Nat.card Y).factorization 2 = 8 := by
    have hpos : Nat.card Y ≠ 0 := Nat.card_pos.ne'
    have h8 : 2 ^ 8 ∣ Nat.card Y := by
      rw [← M.card_S3]
      exact Subgroup.card_dvd_of_le hS3Y
    have hge : 8 ≤ (Nat.card Y).factorization 2 :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hpos).mp h8
    have hlt : ¬ 9 ≤ (Nat.card Y).factorization 2 := fun h =>
      hY9 ((Nat.prime_two.pow_dvd_iff_le_factorization hpos).mpr h)
    omega
  have hc1 : Nat.card (M.S3.subgroupOf Y) = 2 ^ (Nat.card Y).factorization 2 := by
    rw [card_subgroupOf_of_le hS3Y, M.card_S3, hfac]
  have hc2 : Nat.card (S3g.subgroupOf Y) = 2 ^ (Nat.card Y).factorization 2 := by
    rw [card_subgroupOf_of_le hS3gY, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      M.card_S3, hfac]
  let P1 : Sylow 2 Y := Sylow.ofCard _ hc1
  let P2 : Sylow 2 Y := Sylow.ofCard _ hc2
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y P2 P1
  have hn : ∀ x ∈ M.S3, ((c : G) * g) * x * ((c : G) * g)⁻¹ ∈ M.S3 := by
    intro x hx
    have hxg : (⟨g * x * g⁻¹, hS3gY ⟨x, hx, rfl⟩⟩ : Y) ∈ (P2 : Subgroup Y) :=
      Subgroup.mem_subgroupOf.mpr ⟨x, hx, rfl⟩
    have hmem : c * ⟨g * x * g⁻¹, hS3gY ⟨x, hx, rfl⟩⟩ * c⁻¹ ∈ (P1 : Subgroup Y) := by
      rw [← hc, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨_, hxg, by simp [MulAut.conj_apply]⟩
    have := Subgroup.mem_subgroupOf.mp hmem
    simpa [mul_assoc] using this
  have hnL := M.mem_L_of_normalizes_S3 hn
  have hns : ((c : G) * g) * s = s * ((c : G) * g) := by
    have h1 : (c : G) * s = s * c := mem_Cen.mp c.2.1
    have h2 : g * s = s * g := mem_Cen.mp hg
    rw [mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hfix := M.comm_S0_of_mem_CL hs hs1 hnL hns hs'
  have hcy : (c : G) * y = y * c := mem_Cen.mp c.2.2
  calc y = (c : G) * y * (c : G)⁻¹ := by rw [hcy, mul_inv_cancel_right]
    _ = ((c : G) * g) * s' * ((c : G) * g)⁻¹ := by rw [hydef]; group
    _ = s' := by rw [hfix, mul_inv_cancel_right]

@[expose] noncomputable def trS (s : G) :
    Cen s →* Abelianization (M.S3.subgroupOf (Cen s)) :=
  MonoidHom.transfer (Abelianization.of (G := M.S3.subgroupOf (Cen s)))

theorem odd_index_S3
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) :
    ¬ 2 ∣ (M.S3.subgroupOf (Cen s)).index := by
  intro h2
  apply M.not_dvd_card_centralizer hs hs1
  have h := (M.S3.subgroupOf (Cen s)).card_mul_index
  rw [card_subgroupOf_of_le (M.S3_le_Cen hs hs1), M.card_S3] at h
  rw [← h, show 2 ^ 9 = 2 ^ 8 * 2 by norm_num]
  exact Nat.mul_dvd_mul_left _ h2

theorem trS_ne_one
    {s : G} (hs : s ∈ M.S0) (hs1 : s ≠ 1) {s' : G} (hs' : s' ∈ M.S0)
    (hs'1 : s' ≠ 1) :
    M.trS s ⟨s', M.S3_le_Cen hs hs1 (M.S0_le_S3 hs')⟩ ≠ 1 := by
  set x : Cen s := ⟨s', M.S3_le_Cen hs hs1 (M.S0_le_S3 hs')⟩ with hxdef
  have hxH : x ∈ M.S3.subgroupOf (Cen s) := Subgroup.mem_subgroupOf.mpr (M.S0_le_S3 hs')
  have htr := transfer_eq_pow_of_forall (Abelianization.of (G := M.S3.subgroupOf (Cen s)))
    hxH (by
      intro k a ha
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
      have ha' : (a : G)⁻¹ * s' ^ k * a ∈ M.S3 := by
        have := Subgroup.mem_subgroupOf.mp ha
        simpa using this
      have hk : s' ^ k ∈ M.S0 := pow_mem hs' k
      have h := M.conj_S0_eq hs hs1 hk (inv_mem a.2) (by simpa using ha')
      simpa using h)
  rw [trS, htr]
  intro h1
  have hodd := M.odd_index_S3 hs hs1
  have hx2 : (Abelianization.of (⟨x, hxH⟩ : M.S3.subgroupOf (Cen s))) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxH⟩ : M.S3.subgroupOf (Cen s)) ^ 2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, hxdef]
      exact M.S0_elem.2 _ hs'
    rw [this, map_one]
  have hone : Abelianization.of (⟨x, hxH⟩ : M.S3.subgroupOf (Cen s)) = 1 := by
    have hcop : Nat.Coprime 2 (M.S3.subgroupOf (Cen s)).index :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have := pow_gcd_eq_one.2 ⟨hx2, h1⟩
    rwa [hcop, pow_one] at this
  have hmem : (⟨x, hxH⟩ : M.S3.subgroupOf (Cen s)) ∈ commutator (M.S3.subgroupOf (Cen s)) := by
    rw [← Abelianization.ker_of]
    exact hone
  have hle : commutator (M.S3.subgroupOf (Cen s)) ≤
      ((ruV M.L).subgroupOf (Cen s)).subgroupOf (M.S3.subgroupOf (Cen s)) := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have ha := M.S3_le_S (Subgroup.mem_subgroupOf.mp a.2)
    have hb := M.S3_le_S (Subgroup.mem_subgroupOf.mp b.2)
    have := M.comm_mem_V ha hb
    simpa [commutatorElement_def] using this
  have hV : s' ∈ ruV M.L := by
    have := hle hmem
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at this
    exact this
  exact hs'1 (M.eq_one_of_mem_S0_V hs' hV)

end RuDataM

end CFSG.Quasithin.RuType
