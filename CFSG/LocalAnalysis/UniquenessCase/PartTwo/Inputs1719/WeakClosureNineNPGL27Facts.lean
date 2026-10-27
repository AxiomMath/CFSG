module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27Abs
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFF7

open CFSG.QuasithinUnique.A6Facts CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X] {φ : X →* Equiv.Perm (Fin 8)} {Tb : Subgroup X}

theorem IsF7Emb.mul_eq_mul (h : IsF7Emb φ) {a b c d : X}
    (he : Core.cmul (codeN 8 (φ a)) (codeN 8 (φ b)) = Core.cmul (codeN 8 (φ c)) (codeN 8 (φ d))) :
    a * b = c * d :=
  h.code_inj (by rw [code_mul, code_mul, he])

theorem mul_ne_mul_of_code {a b c d : X}
    (he : Core.cmul (codeN 8 (φ a)) (codeN 8 (φ b)) ≠ Core.cmul (codeN 8 (φ c)) (codeN 8 (φ d))) :
    a * b ≠ c * d := by
  intro h
  apply he
  rw [← code_mul, ← code_mul, h]

theorem code_sq_of_sq {x : X} (hx : x ^ 2 = 1) :
    Core.cmul (codeN 8 (φ x)) (codeN 8 (φ x)) = cid := by
  rw [← code_mul, ← pow_two, hx, code_one]

theorem IsF7Emb.sq_of_code (h : IsF7Emb φ) {x : X}
    (hx : Core.cmul (codeN 8 (φ x)) (codeN 8 (φ x)) = cid) : x ^ 2 = 1 := by
  rw [pow_two]
  exact h.eq_one (by rw [code_mul, hx])

theorem IsF7Emb.cube_of_code (h : IsF7Emb φ) {x : X}
    (hx : Core.cmul (Core.cmul (codeN 8 (φ x)) (codeN 8 (φ x))) (codeN 8 (φ x)) = cid) :
    x ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  exact h.eq_one (by rw [code_mul, code_mul, hx])

theorem IsF7Model.pair (hφ : IsF7Model φ Tb) (hTb : IsSylowIn 2 Tb ⊤) (x : X)
    (hx : orderOf x = 2) : ∃ n : X,
      IsPGroup 2 (closure {x, n * x * n⁻¹}) ∧ x * (n * x * n⁻¹) ≠ (n * x * n⁻¹) * x := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have hc1 : codeN 8 (φ x) ≠ cid := fun h => hx1 (hφ.eq_one h)
  obtain ⟨h, hh, c', hc', hhc, m, hm, d, hd, hmd, hne⟩ :=
    pair_check _ (hφ.mem x) (code_sq_of_sq hx2) hc1
  obtain ⟨h', rfl⟩ := hφ.surj h hh
  obtain ⟨c'', rfl⟩ := hφ.surj c' (t_sub _ hc')
  obtain ⟨m', rfl⟩ := hφ.surj m (t_sub _ hm)
  obtain ⟨d', rfl⟩ := hφ.surj d (t_sub _ hd)
  have e1 : h' * x = c'' * h' := hφ.mul_eq_mul hhc
  have e2 : m' * c'' = d' * m' := hφ.mul_eq_mul hmd
  have hne' : c'' * d' ≠ d' * c'' := mul_ne_mul_of_code hne
  have hc''T : c'' ∈ Tb := (hφ.memT _).2 hc'
  have hd'T : d' ∈ Tb := (hφ.memT _).2 hd
  refine ⟨h'⁻¹ * m' * h', ?_, ?_⟩
  · have hxe : x = h'⁻¹ * c'' * h' := by
      rw [mul_assoc, ← e1]
      group
    have hye : h'⁻¹ * m' * h' * x * (h'⁻¹ * m' * h')⁻¹ = h'⁻¹ * d' * h' := by
      have : m' * c'' * m'⁻¹ = d' := by rw [e2]; group
      rw [hxe, ← this]
      group
    have hle : closure {x, h'⁻¹ * m' * h' * x * (h'⁻¹ * m' * h')⁻¹} ≤
        Tb.map (MulAut.conj h'⁻¹).toMonoidHom := by
      rw [closure_le]
      intro z hz
      rcases hz with rfl | hz
      · rw [hxe]
        exact ⟨c'', hc''T, by simp⟩
      · rw [Set.mem_singleton_iff] at hz
        rw [hz, hye]
        exact ⟨d', hd'T, by simp⟩
    exact (hTb.isPGroup.map _).to_le hle
  · intro heq
    apply hne'
    have hxe : x = h'⁻¹ * c'' * h' := by
      rw [mul_assoc, ← e1]
      group
    have hye : h'⁻¹ * m' * h' * x * (h'⁻¹ * m' * h')⁻¹ = h'⁻¹ * d' * h' := by
      have : m' * c'' * m'⁻¹ = d' := by rw [e2]; group
      rw [hxe, ← this]
      group
    rw [hye, hxe] at heq
    have := congrArg (fun z => h' * z * h'⁻¹) heq
    simpa [mul_assoc] using this

variable [Finite X]

@[expose] def Vsub (φ : X →* Equiv.Perm (Fin 8)) (i : Fin 4) : Subgroup X :=
  subL φ (row i).V (row_V_one i) (row_V_mul i)

@[expose] def Ksub (φ : X →* Equiv.Perm (Fin 8)) (i : Fin 4) : Subgroup X :=
  subL φ (row i).K (row_K_one i) (row_K_mul i)

@[expose] def Ysub (φ : X →* Equiv.Perm (Fin 8)) (i : Fin 4) : Subgroup X :=
  subL φ (row i).Y (row_Y_one i) (row_Y_mul i)

@[expose] def Usub (φ : X →* Equiv.Perm (Fin 8)) (i : Fin 4) : Subgroup X :=
  subL φ (row i).U (row_U_one i) (row_U_mul i)

@[expose] def Msub (φ : X →* Equiv.Perm (Fin 8)) (i : Fin 4) : Subgroup X :=
  subL φ (row i).M (row_M_one i) (row_M_mul i)

theorem mem_Vsub {i : Fin 4} {x : X} : x ∈ Vsub φ i ↔ codeN 8 (φ x) ∈ (row i).V := Iff.rfl

theorem mem_Ksub {i : Fin 4} {x : X} : x ∈ Ksub φ i ↔ codeN 8 (φ x) ∈ (row i).K := Iff.rfl

theorem IsF7Model.classify (hφ : IsF7Model φ Tb) {A : Subgroup X} (hA : A ≤ Tb)
    (hAe : IsElemAbelian 2 A) (h4 : 4 ≤ Nat.card A) : ∃ i : Fin 4, A = Vsub φ i := by
  obtain ⟨hcomm, hsq⟩ := hAe
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_ne_one_ne_of_four_le h4
  obtain ⟨i, -, hai, hbi, hV, hC⟩ := ident_check _ ((hφ.memT a).1 (hA ha)) _
    ((hφ.memT b).1 (hA hb)) (code_sq_of_sq (hsq a ha)) (code_sq_of_sq (hsq b hb))
    (fun h => ha1 (hφ.eq_one h)) (fun h => hb1 (hφ.eq_one h))
    (fun h => hab (hφ.code_inj h)) (by rw [← code_mul, ← code_mul, hAc a ha b hb])
  refine ⟨i, le_antisymm (fun x hx => ?_) (fun x hx => ?_)⟩
  · refine mem_Vsub.2 (hC _ ((hφ.memT x).1 (hA hx)) ?_ ?_)
    · rw [← code_mul, ← code_mul, hAc x hx a ha]
    · rw [← code_mul, ← code_mul, hAc x hx b hb]
  · rcases hV _ (mem_Vsub.1 hx) with h | h | h | h
    · rw [hφ.eq_one h]
      exact one_mem A
    · rw [hφ.code_inj h]
      exact ha
    · rw [hφ.code_inj h]
      exact hb
    · rw [hφ.code_inj (h.trans (code_mul a b).symm)]
      exact mul_mem ha hb

theorem IsF7Emb.card_Ksub (h : IsF7Emb φ) (i : Fin 4) : Nat.card (Ksub φ i) = (row i).K.length :=
  h.card_eq (fun _ => Iff.rfl) (row_K_sub i) (row_K_nodup i)

theorem IsF7Emb.card_Ysub (h : IsF7Emb φ) (i : Fin 4) : Nat.card (Ysub φ i) = 3 := by
  rw [h.card_eq (fun _ => Iff.rfl) (fun y hy => row_K_sub i _ (row_Y_sub i y hy))
    (row_Y_nodup i), row_Y_length]

theorem IsF7Model.card_KT (hφ : IsF7Model φ Tb) (i : Fin 4) :
    Nat.card (Ksub φ i ⊓ Tb : Subgroup X) =
      ((row i).K.filter fun k => decide (k ∈ tLit)).length := by
  refine hφ.card_eq (fun x => ?_) (fun c hc => row_K_sub i _ (List.mem_filter.1 hc).1)
    ((row_K_nodup i).filter _)
  rw [mem_inf, mem_Ksub, hφ.memT, List.mem_filter, decide_eq_true_iff]

theorem IsF7Emb.oTwoPTwo_Ksub (h : IsF7Emb φ) (i : Fin 4) :
    E1.oTwoPTwo ↥(Ksub φ i) 3 = ⊤ := by
  refine oTwoPTwo_eq_top_of (U := Usub φ i) (M := Msub φ i) (fun k hk u hu => ?_)
    (fun k hk m hm => ?_)
    (fun u hu => h.sq_of_code (row_U_sq i _ hu)) (fun m hm => ?_) (fun k hk => ?_)
  · obtain ⟨u', hu', he⟩ := row_U_norm i _ hk _ hu
    obtain ⟨u'', rfl⟩ := h.surj u' (row_K_sub i _ (row_U_sub i _ hu'))
    have : k * u = u'' * k := h.mul_eq_mul he
    rw [this, mul_inv_cancel_right]
    exact hu'
  · obtain ⟨m', hm', he⟩ := row_M_norm i _ hk _ hm
    obtain ⟨m'', rfl⟩ := h.surj m' (row_K_sub i _ (row_M_sub i _ hm'))
    have : k * m = m'' * k := h.mul_eq_mul he
    rw [this, mul_inv_cancel_right]
    exact hm'
  · change codeN 8 (φ (m ^ 3)) ∈ (row i).U
    rw [pow_succ, pow_two, code_mul, code_mul]
    exact row_M_cube i _ hm
  · change codeN 8 (φ (k ^ 2)) ∈ (row i).M
    rw [pow_two, code_mul]
    exact row_K_sq i _ hk

theorem IsF7Model.twoPTwoIrred (hφ : IsF7Model φ Tb) (hTb : IsSylowIn 2 Tb ⊤) (i : Fin 4) :
    TwoPTwoIrred (Ksub φ i) (Ksub φ i ⊓ Tb) (Ysub φ i) 3 := by
  have hK := hφ.card_Ksub i
  have hKT := hφ.card_KT i
  have hY := hφ.card_Ysub i
  have hKT3 := row_KT_length i
  have hK9 := row_K_nine i
  refine ⟨⟨Nat.prime_three, by decide, hφ.oTwoPTwo_Ksub i, ⟨inf_le_left,
    hTb.isPGroup.to_le inf_le_right, ?_⟩, ⟨fun y hy => row_Y_sub i _ hy,
    fun y => ⟨1, Subtype.ext ?_⟩, ?_⟩⟩, irredOnFrattiniQuot_of_card_prime Nat.prime_three hY⟩
  · have hr := relIndex_mul_card (Ksub φ i ⊓ Tb) (Ksub φ i)
    rw [inf_right_comm, inf_idem, hKT, hK, ← hKT3] at hr
    have hpos : 0 < ((row i).K.filter fun k => decide (k ∈ tLit)).length := by
      have := List.length_pos_of_mem (row_K_one i)
      omega
    have h3 : (Ksub φ i ⊓ Tb).relIndex (Ksub φ i) = 3 :=
      Nat.eq_of_mul_eq_mul_right hpos (hr.trans (mul_comm _ _))
    rw [h3]
    decide
  · simpa using hφ.cube_of_code (row_Y_cube i _ y.2)
  · have hr := relIndex_mul_card (Ysub φ i) (Ksub φ i)
    have hYK : Ysub φ i ⊓ Ksub φ i = Ysub φ i := inf_eq_left.2 fun y hy => row_Y_sub i _ hy
    rw [hYK, hY, hK] at hr
    intro h3
    apply hK9
    rw [← hr]
    exact Nat.mul_dvd_mul_right h3 3

theorem IsF7Model.table (hφ : IsF7Model φ Tb) (hTb : IsSylowIn 2 Tb ⊤) (A : Subgroup X)
    (hA : A ≤ Tb) (hAe : IsElemAbelian 2 A) (h4 : 4 ≤ Nat.card A) :
    ∃ (K Y : Subgroup X) (p : ℕ), A ≤ K ∧ TwoPTwoIrred K (K ⊓ Tb) Y p ∧
      CFSG.Quasithin.coreIn (Tb ⊓ centralizer (A : Set X)) Tb ≤ K ⊓ Tb ∧
      (∀ R : Subgroup X, A ≤ R → R ≤ K ⊓ Tb →
        ¬ K ⊔ (Tb ⊓ normalizer ((K ⊓ Tb : Subgroup X) : Set X)) ≤ normalizer (R : Set X)) ∧
      (p = 3 ∨ ∀ H : Subgroup X, Tb ≤ H → H = Tb ∨ H = ⊤) := by
  obtain ⟨i, rfl⟩ := hφ.classify hA hAe h4
  refine ⟨Ksub φ i, Ysub φ i, 3, fun v hv => row_V_sub i _ hv, hφ.twoPTwoIrred hTb i,
    ?_, ?_, Or.inl rfl⟩
  · refine (coreIn_le_right _ _).trans fun x hx => ⟨?_, hx.1⟩
    refine mem_Ksub.2 (row_cent i _ ((hφ.memT x).1 hx.1) fun v hv => ?_)
    obtain ⟨v', rfl⟩ := hφ.surj v (row_K_sub i _ (row_V_sub i _ hv))
    rw [← code_mul, ← code_mul, (mem_centralizer_iff.1 hx.2) v' hv]
  · intro R hVR hRS hJ
    obtain ⟨k, hk, v, hv, hne⟩ := row_wit i
    obtain ⟨k', rfl⟩ := hφ.surj k (row_K_sub i _ hk)
    obtain ⟨v', rfl⟩ := hφ.surj v (row_K_sub i _ (row_V_sub i _ hv))
    have hkN : k' ∈ normalizer (R : Set X) := hJ (mem_sup_left hk)
    have hc : k' * v' * k'⁻¹ ∈ R := (mem_normalizer_iff.1 hkN v').1 (hVR hv)
    have hcT : k' * v' * k'⁻¹ ∈ Tb := (hRS hc).2
    apply hne _ ((hφ.memT _).1 hcT)
    rw [← code_mul, ← code_mul, inv_mul_cancel_right]

theorem IsF7Model.close (hφ : IsF7Model φ Tb) (E : Subgroup X) (hE : E ≤ Tb)
    (hEn : Tb ≤ normalizer (E : Set X)) (hEe : IsElemAbelian 2 E) (h4 : 4 ≤ Nat.card E) : False := by
  obtain ⟨i, rfl⟩ := hφ.classify hE hEe h4
  obtain ⟨t, ht, v, hv, hne⟩ := row_notNormal i
  obtain ⟨t', rfl⟩ := hφ.surj t (t_sub _ ht)
  obtain ⟨v', rfl⟩ := hφ.surj v (row_K_sub i _ (row_V_sub i _ hv))
  have htN : t' ∈ normalizer (Vsub φ i : Set X) := hEn ((hφ.memT t').2 ht)
  have hc : t' * v' * t'⁻¹ ∈ Vsub φ i := (mem_normalizer_iff.1 htN v').1 hv
  apply hne _ (mem_Vsub.1 hc)
  rw [← code_mul, ← code_mul, inv_mul_cancel_right]

end CFSG.LocalAnalysis.WeakClosure81.NFF7
