module

public import CFSG.Quasithin.H13.U3L14E5

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_pCoreOf_le {K J : Subgroup G} (hKJ : K ≤ J) :
    K ⊓ pCoreOf 2 J ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun k hk => mem_normalizer_inf (le_normalizer hk)
      (LieType.BorelTits.le_normalizer_pCoreOf 2 J (hKJ hk)))
    ((LieType.BorelTits.pCoreOf_isPGroup 2 J).to_le inf_le_right)

omit [Finite G] in
theorem normalizer_le_of_characteristic {B C : Subgroup G} (hCB : C ≤ B)
    (hc : (C.subgroupOf B).Characteristic) :
    normalizer (B : Set G) ≤ normalizer (C : Set G) := by
  have key : ∀ g ∈ normalizer (B : Set G), ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc'
    set φ := B.normalizerMonoidHom ⟨g, hg⟩ with hφ
    have hinv : (φ⁻¹ : MulAut ↥B) (φ ⟨c, hCB hc'⟩) = ⟨c, hCB hc'⟩ := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have h2 : φ ⟨c, hCB hc'⟩ ∈ (C.subgroupOf B).comap (φ⁻¹).toMonoidHom := by
      rw [mem_comap, MulEquiv.coe_toMonoidHom, hinv]
      exact mem_subgroupOf.mpr hc'
    rw [hc.fixed, mem_subgroupOf, hφ, Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
    exact h2
  intro g hg
  rw [mem_normalizer_iff]
  intro c
  refine ⟨fun h => key g hg c h, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  simpa [mul_assoc] using this

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem charTwo_J {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) :
    (K ⊔ Lp ⊔ T) ⊓ centralizer (pCoreOf 2 (K ⊔ Lp ⊔ T) : Set G) ≤ pCoreOf 2 (K ⊔ Lp ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := K ⊔ Lp ⊔ T with hJ
  have hJG : J ≤ A6.g1 T V := sup_le (sup_le (le_of_mem_cComp hD.mem) S.Lp_G1) S.T_G1
  have hTJ : T ≤ J := le_sup_right
  have hQ1T : pCoreOf 2 (A6.g1 T V) ≤ T := S.Q1_T
  have hQJ : pCoreOf 2 (A6.g1 T V) ≤ pCoreOf 2 J :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQ1T.trans hTJ)
      (hJG.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  intro g hg
  obtain ⟨hgJ, hgC⟩ := mem_inf.mp hg
  have h1 : g ∈ A6.g1 T V ⊓ centralizer (pCoreOf 2 (A6.g1 T V) : Set G) :=
    mem_inf.mpr ⟨hJG hgJ, centralizer_le hQJ hgC⟩
  exact hQJ (S.charTwo_G1 h1)

theorem block_of_stmt13_3_10 (h1332 : Stmt13_3_2) (h1310 : Stmt13_3_10)
    (hA5 : IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))))
    (hB : ¬ normalizer (baum (pCoreOf 2 (Lp ⊔ T)) : Set G) ≤ normalizer (L : Set G)) :
    IsLnBlock L 3 ∨ H13.IsA6Block L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hA6, hL3⟩ := h1310 G T L V Lp S.h13 S.irr S.zv S.Lp_def.1 S.Lp_def.2
  have hchar : ¬ CharNormal (baum (pCoreOf 2 (Lp ⊔ T))) (L ⊔ T) := by
    rintro ⟨C, hCB, hC1, hc, hLTC⟩
    apply hB
    refine (normalizer_le_of_characteristic hCB hc).trans ?_
    have hC2 : IsPGroup 2 C := (LieType.BorelTits.pCoreOf_isPGroup 2 (Lp ⊔ T)).to_le
      (hCB.trans inf_le_left)
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨C, hC1, hC2, rfl⟩ : IsTwoLocal (normalizer (C : Set G)))
    have := S.uniq M' hM' (hLTC.trans hM'le)
    exact this ▸ hM'le
  obtain ⟨-, -, ⟨-, hall⟩, -⟩ := h1332 G T L S.h13 L S.h13.faithful
  obtain ⟨-, -, -, hab, hmod⟩ := hall V S.irr
  rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, hc2, -⟩ | ⟨hl, -, -⟩ | ⟨hu, -, -⟩
  ·
    obtain ⟨e⟩ := A6.nonempty_mulEquiv_of_realizes (A6.altDn_faithful (by norm_num)) h5
    exact (hA5.false e).elim
  ·
    obtain ⟨h1, h2⟩ := hA6 (Or.inl (A6.nonempty_mulEquiv_of_realizes
      (A6.altDn_faithful (by norm_num)) h6))
    rcases h1 with h | h | h
    · exact (hchar h).elim
    · exact Or.inr h
    · exact (hB (h2 h)).elim
  ·
    rw [S.zv, card_bot] at hc2
    exact absurd hc2 (by norm_num)
  ·
    rcases hL3 hl with h | h
    · exact (hchar h).elim
    · exact Or.inl h
  ·
    obtain ⟨h1, h2⟩ := hA6 (Or.inr hu)
    rcases h1 with h | ⟨-, ⟨e⟩, -⟩ | h
    · exact (hchar h).elim
    · exfalso
      have h3 := card_of_statedClassicalModel_psu_three_three
        (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hu)
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h3
      exact absurd h3 (by decide)
    · exact (hB (h2 h)).elim

theorem mem_normalizer_I {K I : Subgroup G} (hD : KData14 T L V V₂ Lp K) (hg : ¬ Lp ≤ K)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hB : IsLnBlock L 3 ∨ H13.IsA6Block L)
    (hI : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T I) (hZ : I ⊓ centralizer (K : Set G) = ⊥)
    (F : A5.Frame T K I) {x : G} (hx : x ∈ Lp) (hxo : Odd (orderOf x)) (hx1 : x ≠ 1) :
    x ∈ normalizer (I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hxI
  have hx3 : x ^ 3 = 1 := S.odd_pow_three hx hxo
  have hc16 := S.relIndex_R1_le_sixteen hB hx hx3
  set R := pCoreOf 2 (Lp ⊔ T) with hR
  set N := pCoreOf 2 (K ⊔ T) with hN
  set C := centralizer ({x} : Set G) with hC
  have hNR : N ≤ R := S.pCoreOf_KT_le_R1 hD
  have hRN : R ≤ normalizer (N : Set G) :=
    S.R1_le_T.trans (le_sup_right.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T)))
  have hxN : x ∈ normalizer (N : Set G) := S.mem_normalizer_pCoreOf_KT hD hx
  have hxR : x ∈ normalizer (R : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 (Lp ⊔ T) (mem_sup_left hx)
  have hR2 : IsPGroup 2 R := LieType.BorelTits.pCoreOf_isPGroup 2 (Lp ⊔ T)
  have hmul := relIndex_centralizer_eq_mul (x := x) hNR hRN
  have hIC : I ⊓ C = ⊥ := by
    set W := I ⊓ I.map (MulAut.conj x).toMonoidHom with hW
    have hKW : K ≤ normalizer (W : Set G) := by
      intro k hk
      refine mem_normalizer_inf (hI.2.2.1 hk) ?_
      have hk' : x⁻¹ * k * x ∈ K := by
        have := (mem_normalizer_iff.mp (hD.Lp_K (inv_mem hx)) k).mp hk
        simpa using this
      rw [mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨i, hi, rfl⟩
        refine ⟨(x⁻¹ * k * x) * i * (x⁻¹ * k * x)⁻¹,
          (mem_normalizer_iff.mp (hI.2.2.1 hk') i).mp hi, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro ⟨i, hi, hie⟩
        refine ⟨(x⁻¹ * k * x)⁻¹ * i * (x⁻¹ * k * x)⁻¹⁻¹, ?_, ?_⟩
        · exact (mem_normalizer_iff.mp (hI.2.2.1 (inv_mem hk')) i).mp hi
        · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hie ⊢
          calc x * ((x⁻¹ * k * x)⁻¹ * i * (x⁻¹ * k * x)⁻¹⁻¹) * x⁻¹
              = k⁻¹ * (x * i * x⁻¹) * k := by group
            _ = y := by rw [hie]; group
    rcases hI.2.2.2.2.2.1 W (by rw [hZ]; exact bot_le) inf_le_left hKW with h | h
    · rw [eq_bot_iff]
      intro v hv'
      obtain ⟨hv, hvC⟩ := mem_inf.mp hv'
      have hvW : v ∈ W := by
        refine mem_inf.mpr ⟨hv, ⟨v, hv, ?_⟩⟩
        rw [mem_centralizer_singleton_iff] at hvC
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [hvC]
          _ = v := by group
      rw [h, hZ] at hvW
      exact hvW
    · exfalso
      apply hxI
      have hle : I ≤ I.map (MulAut.conj x).toMonoidHom := fun v hv =>
        (mem_inf.mp (h.symm ▸ hv : v ∈ W)).2
      have heq : I.map (MulAut.conj x).toMonoidHom = I :=
        (Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective
          (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective).le).symm
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [← heq]
        exact ⟨y, hy, rfl⟩
      · intro hy
        rw [← heq] at hy
        obtain ⟨z, hz, hze⟩ := hy
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hze
        have : z = y := mul_left_cancel (mul_right_cancel hze)
        rw [← this]
        exact hz
  have hIN : I ≤ N := fun v hv => (mem_reducedAggregate' (hI.1 hv)).1
  have hcI : C.relIndex I = 16 := by
    rw [← inf_relIndex_right C I, inf_comm, hIC, relIndex_bot_left, F.card_I]
  have hcN : 16 ≤ C.relIndex N := hcI ▸ relIndex_centralizer_le hIN
  rcases relIndex_sup_eq_one_or hx3 hR2 hNR hRN hxN hxR with h1 | h1
  · apply S.kplus_factor hD hA5 hx hxo hx1
    intro t ht
    have htR : t ∈ R := S.inf_le_R1 hD hg ht
    rw [relIndex_eq_one] at h1
    obtain ⟨n, hn, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer
      (inf_le_left.trans hRN)).1 (h1 htR)
    have hcx : x * c = c * x := (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2).symm
    have hmemN : (n * c)⁻¹ * (x * (n * c) * x⁻¹) ∈ N := by
      have h2 : (n * c)⁻¹ * (x * (n * c) * x⁻¹) = c⁻¹ * (n⁻¹ * (x * n * x⁻¹)) * c := by
        calc (n * c)⁻¹ * (x * (n * c) * x⁻¹) = c⁻¹ * n⁻¹ * (x * n * x⁻¹ * (x * c) * x⁻¹) := by
              group
          _ = c⁻¹ * (n⁻¹ * (x * n * x⁻¹)) * c := by rw [hcx]; group
      rw [h2]
      have h3 : n⁻¹ * (x * n * x⁻¹) ∈ N :=
        mul_mem (inv_mem hn) ((mem_normalizer_iff.mp hxN n).mp hn)
      have h4 := (mem_normalizer_iff.mp (hRN (inv_mem (mem_inf.mp hc).1)) _).mp h3
      simpa using h4
    have hmemK : (n * c)⁻¹ * (x * (n * c) * x⁻¹) ∈ K :=
      mul_mem (inv_mem (mem_inf.mp ht).2)
        ((mem_normalizer_iff.mp (hD.Lp_K hx) _).mp (mem_inf.mp ht).2)
    exact inf_pCoreOf_le le_sup_left (mem_inf.mpr ⟨hmemK, hmemN⟩)
  · have : 64 ≤ C.relIndex R := by
      rw [hmul]
      calc 64 = 4 * 16 := by norm_num
        _ ≤ _ := Nat.mul_le_mul h1 hcN
    omega

theorem comm_le_I {K I : Subgroup G} (hD : KData14 T L V V₂ Lp K) (hg : ¬ Lp ≤ K)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hB : IsLnBlock L 3 ∨ H13.IsA6Block L)
    (hI : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T I) (hTI : T ≤ normalizer (I : Set G))
    (hIe : IsElemAbelian 2 I) (hCK : K ⊓ centralizer (I : Set G) = pCoreOf 2 K)
    (hLpI : Lp ≤ normalizer (I : Set G)) {x : G} (hx : x ∈ Lp) (hxo : Odd (orderOf x))
    (hx1 : x ≠ 1) :
    ∀ q ∈ pCoreOf 2 (K ⊔ Lp ⊔ T), x * q * x⁻¹ * q⁻¹ ∈ I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx3 : x ^ 3 = 1 := S.odd_pow_three hx hxo
  have hc16 := S.relIndex_R1_le_sixteen hB hx hx3
  set J := K ⊔ Lp ⊔ T with hJ
  set Q := pCoreOf 2 J with hQ
  set R := pCoreOf 2 (Lp ⊔ T) with hR
  set C := centralizer ({x} : Set G) with hC
  have hI2 : IsPGroup 2 I := fun v => ⟨1, Subtype.ext (by simpa using hIe.2 v v.2)⟩
  have hJI : J ≤ normalizer (I : Set G) := sup_le (sup_le hI.2.2.1 hLpI) hTI
  have hIT : I ≤ T := fun v hv =>
    (pCoreOf_two_le_of_sylowIn le_sup_right (S.syl (le_sup_right : T ≤ K ⊔ T)).2.1
      (S.syl (le_sup_right : T ≤ K ⊔ T)).2.2) ((mem_reducedAggregate' (hI.1 hv)).1)
  have hIQ : I ≤ Q :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hIT.trans le_sup_right) hJI hI2
  have hQT : Q ≤ T :=
    pCoreOf_two_le_of_sylowIn le_sup_right (S.syl (le_sup_right : T ≤ J)).2.1
      (S.syl (le_sup_right : T ≤ J)).2.2
  have hLpTJ : Lp ⊔ T ≤ J := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hQR : Q ≤ R :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      (hLpTJ.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 J))
      (LieType.BorelTits.pCoreOf_isPGroup 2 J)
  have hRQ : R ≤ normalizer (Q : Set G) :=
    (S.R1_le_T.trans le_sup_right).trans (LieType.BorelTits.le_normalizer_pCoreOf 2 J)
  have hxJ : x ∈ J := mem_sup_left (mem_sup_right hx)
  have hxQ : x ∈ normalizer (Q : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 J hxJ
  have hxR : x ∈ normalizer (R : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 (Lp ⊔ T) (mem_sup_left hx)
  have hR2 : IsPGroup 2 R := LieType.BorelTits.pCoreOf_isPGroup 2 (Lp ⊔ T)
  have hQ2 : IsPGroup 2 Q := LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hxI : x ∈ normalizer (I : Set G) := hLpI hx
  have hQI : Q ≤ normalizer (I : Set G) := (LieType.BorelTits.pCoreOf_le 2 J).trans hJI
  have hcI : 4 ≤ C.relIndex I := by
    refine four_le_relIndex_centralizer hx3 hxI hI2 fun hle => ?_
    apply S.kAct_ne_one hD hx hxo hx1
    refine (kAct_eq_one_iff _).2 fun k hk => ?_
    rw [← hCK]
    refine mem_inf.mpr ⟨mul_mem (inv_mem hk) ((mem_normalizer_iff.mp (hD.Lp_K hx) k).mp hk), ?_⟩
    rw [mem_centralizer_iff]
    intro v hv
    have hv' : k * v * k⁻¹ ∈ I := (mem_normalizer_iff.mp (hI.2.2.1 hk) v).mp hv
    have h1 := mem_centralizer_singleton_iff.mp (hle hv)
    have h2 := mem_centralizer_singleton_iff.mp (hle hv')
    calc v * (k⁻¹ * (x * k * x⁻¹)) = k⁻¹ * ((k * v * k⁻¹) * x) * k * x⁻¹ := by group
      _ = k⁻¹ * (x * (k * v * k⁻¹)) * k * x⁻¹ := by rw [h2]
      _ = k⁻¹ * x * k * x⁻¹ * (x * v) * x⁻¹ := by group
      _ = k⁻¹ * x * k * x⁻¹ * (v * x) * x⁻¹ := by rw [← h1]
      _ = k⁻¹ * (x * k * x⁻¹) * v := by group
  have hfactor : 4 ≤ (Q ⊔ (R ⊓ C)).relIndex R := by
    rcases relIndex_sup_eq_one_or hx3 hR2 hQR hRQ hxQ hxR with h1 | h1
    · exfalso
      apply S.kplus_factor hD hA5 hx hxo hx1
      intro t ht
      have htR : t ∈ R := S.inf_le_R1 hD hg ht
      rw [relIndex_eq_one] at h1
      obtain ⟨n, hn, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer
        (inf_le_left.trans hRQ)).1 (h1 htR)
      have hcx : x * c = c * x := (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2).symm
      have hmemQ : (n * c)⁻¹ * (x * (n * c) * x⁻¹) ∈ Q := by
        have h2 : (n * c)⁻¹ * (x * (n * c) * x⁻¹) = c⁻¹ * (n⁻¹ * (x * n * x⁻¹)) * c := by
          calc (n * c)⁻¹ * (x * (n * c) * x⁻¹) =
                c⁻¹ * n⁻¹ * (x * n * x⁻¹ * (x * c) * x⁻¹) := by group
            _ = c⁻¹ * (n⁻¹ * (x * n * x⁻¹)) * c := by rw [hcx]; group
        rw [h2]
        have h3 : n⁻¹ * (x * n * x⁻¹) ∈ Q :=
          mul_mem (inv_mem hn) ((mem_normalizer_iff.mp hxQ n).mp hn)
        have h4 := (mem_normalizer_iff.mp (hRQ (inv_mem (mem_inf.mp hc).1)) _).mp h3
        simpa using h4
      have hmemK : (n * c)⁻¹ * (x * (n * c) * x⁻¹) ∈ K :=
        mul_mem (inv_mem (mem_inf.mp ht).2)
          ((mem_normalizer_iff.mp (hD.Lp_K hx) _).mp (mem_inf.mp ht).2)
      have hKJ : K ≤ J := le_sup_left.trans le_sup_left
      exact inf_pCoreOf_le hKJ (mem_inf.mpr ⟨hmemK, hmemQ⟩)
    · exact h1
  have hmulR := relIndex_centralizer_eq_mul (x := x) hQR hRQ
  have hmulQ := relIndex_centralizer_eq_mul (x := x) hIQ hQI
  have hone : (I ⊔ (Q ⊓ C)).relIndex Q = 1 := by
    have hpos : 0 < (I ⊔ (Q ⊓ C)).relIndex Q :=
      Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := (I ⊔ (Q ⊓ C)).subgroupOf Q))
    by_contra hne
    have h2 : 2 ≤ (I ⊔ (Q ⊓ C)).relIndex Q := by omega
    have : 32 ≤ C.relIndex R := by
      rw [hmulR, hmulQ]
      calc 32 = 4 * (2 * 4) := by norm_num
        _ ≤ _ := Nat.mul_le_mul hfactor (Nat.mul_le_mul h2 hcI)
    omega
  have hQeq : Q ≤ I ⊔ (Q ⊓ C) := relIndex_eq_one.mp hone
  intro q hq
  obtain ⟨i, hi, c, hc, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer
    (inf_le_left.trans hQI)).1 (hQeq hq)
  have hcx : x * c = c * x := (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2).symm
  have : x * (i * c) * x⁻¹ * (i * c)⁻¹ = x * i * x⁻¹ * i⁻¹ := by
    calc x * (i * c) * x⁻¹ * (i * c)⁻¹ = x * i * x⁻¹ * (x * c) * x⁻¹ * c⁻¹ * i⁻¹ := by group
      _ = x * i * x⁻¹ * i⁻¹ := by rw [hcx]; group
  rw [this]
  exact mul_mem ((mem_normalizer_iff.mp hxI i).mp hi) (inv_mem hi)

theorem false_of_A5 (h1332 : Stmt13_3_2) (h1310 : Stmt13_3_10)
    (hA5L : IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5)))) {K : Subgroup G}
    (hD : KData14 T L V V₂ Lp K) (hg : ¬ Lp ≤ K)
    (hA5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨I, hI, hZ, hTI, hIe, hNL, ⟨F⟩⟩ := S.exists_I h1332 hD hA5
  have hKI : K ≤ normalizer (I : Set G) := hI.2.2.1
  have hKn : (K.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hD.T_K)
  have hO : pCoreOf 2 K ≤ centralizer (I : Set G) := by
    have h1 : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
      CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K _ le_sup_left hKn
    intro k hk
    rw [mem_centralizer_iff]
    intro v hv
    exact ((mem_reducedAggregate' (hI.1 hv)).2.1 k (h1 hk)).symm
  have hCK : K ⊓ centralizer (I : Set G) = pCoreOf 2 K :=
    le_antisymm (inf_centralizer_le hD.quasi hA5 hKI hO hZ hI.2.1)
      (le_inf (LieType.BorelTits.pCoreOf_le 2 K) hO)
  have hCT := S.inf_centralizer_eq hD hI hTI hCK.le
  have hIT : I ≤ T := fun v hv =>
    (pCoreOf_two_le_of_sylowIn le_sup_right (S.syl (le_sup_right : T ≤ K ⊔ T)).2.1
      (S.syl (le_sup_right : T ≤ K ⊔ T)).2.2) ((mem_reducedAggregate' (hI.1 hv)).1)
  have hB := S.block_of_stmt13_3_10 h1332 h1310 hA5L
    (S.not_normalizer_baum_le hD hg hA5 F hIe hIT hCT hCK)
  have hodd : ∀ x ∈ Lp, Odd (orderOf x) → x ≠ 1 → x ∈ normalizer (I : Set G) :=
    fun x hx hxo hx1 => S.mem_normalizer_I hD hg hA5 hB hI hZ F hx hxo hx1
  have hLpI : Lp ≤ normalizer (I : Set G) := by
    rw [S.Lp_eq]
    refine (closure_le _).2 fun x hx => ?_
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · exact hodd x hx.1 hx.2 hx1
  set J := K ⊔ Lp ⊔ T with hJ
  set Q := pCoreOf 2 J with hQ
  have hJI : J ≤ normalizer (I : Set G) := sup_le (sup_le hKI hLpI) hTI
  have hJK : J ≤ normalizer (K : Set G) := sup_le (sup_le le_normalizer hD.Lp_K) hD.T_K
  have hJQ : J ≤ normalizer (Q : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 J
  let Csub : Subgroup G :=
    { carrier := {g | g ∈ J ∧ ∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ I}
      one_mem' := ⟨one_mem _, fun q _ => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, fun q hq => by
        have h1 := hb.2 q hq
        have h2 := ha.2 q hq
        have h3 : a * (b * q * b⁻¹ * q⁻¹) * a⁻¹ ∈ I :=
          (mem_normalizer_iff.mp (hJI ha.1) _).mp h1
        have : a * b * q * (a * b)⁻¹ * q⁻¹ =
            (a * (b * q * b⁻¹ * q⁻¹) * a⁻¹) * (a * q * a⁻¹ * q⁻¹) := by group
        rw [this]
        exact mul_mem h3 h2⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun q hq => by
        have hq' : a⁻¹ * q * a ∈ Q := by
          have := (mem_normalizer_iff.mp (hJQ (inv_mem ha.1)) q).mp hq
          simpa using this
        have h1 := ha.2 _ hq'
        have : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = (a * (a⁻¹ * q * a) * a⁻¹ * (a⁻¹ * q * a)⁻¹)⁻¹ := by group
        rw [this]
        exact inv_mem h1⟩ }
  have hCsubJ : Csub ≤ J := fun g hg => hg.1
  have hJC : J ≤ normalizer (Csub : Set G) := by
    have key : ∀ j ∈ J, ∀ g ∈ Csub, j * g * j⁻¹ ∈ Csub := by
      intro j hj g hg
      refine ⟨mul_mem (mul_mem hj hg.1) (inv_mem hj), fun q hq => ?_⟩
      have hq' : j⁻¹ * q * j ∈ Q := by
        have := (mem_normalizer_iff.mp (hJQ (inv_mem hj)) q).mp hq
        simpa using this
      have h1 := hg.2 _ hq'
      have h2 : j * (g * (j⁻¹ * q * j) * g⁻¹ * (j⁻¹ * q * j)⁻¹) * j⁻¹ ∈ I :=
        (mem_normalizer_iff.mp (hJI hj) _).mp h1
      have : j * g * j⁻¹ * q * (j * g * j⁻¹)⁻¹ * q⁻¹ =
          j * (g * (j⁻¹ * q * j) * g⁻¹ * (j⁻¹ * q * j)⁻¹) * j⁻¹ := by group
      rw [this]
      exact h2
    intro j hj
    rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => key j hj g hg, fun hg => ?_⟩
    have := key j⁻¹ (inv_mem hj) _ hg
    simpa [mul_assoc] using this
  have hLpC : Lp ≤ Csub := by
    rw [S.Lp_eq]
    refine (closure_le _).2 fun x hx => ?_
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · exact ⟨mem_sup_left (mem_sup_right hx.1), S.comm_le_I hD hg hA5 hB hI hTI hIe hCK hLpI
        hx.1 hx.2 hx1⟩
  have hKC : K ≤ Csub := by
    rw [← hD.eqLp]
    refine (commutator_mono le_rfl hLpC).trans ?_
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((le_sup_left.trans le_sup_left : K ≤ J).trans hJC)
  set D := Csub ⊓ centralizer (I : Set G) with hDdef
  have hodd1 : ∀ d ∈ D, Odd (orderOf d) → d = 1 := by
    intro d hd hdo
    obtain ⟨hdC, hdI⟩ := mem_inf.mp hd
    have hdQ : d ∈ centralizer (Q : Set G) := by
      rw [mem_centralizer_iff]
      intro q hq
      obtain ⟨i, hi⟩ : ∃ i, i = d * q * d⁻¹ * q⁻¹ := ⟨_, rfl⟩
      have hiI : i ∈ I := by rw [hi]; exact hdC.2 q hq
      have hdi : d * i = i * d := (mem_centralizer_iff.mp hdI i hiI).symm
      have hpow : ∀ n : ℕ, d ^ n * q * (d ^ n)⁻¹ = i ^ n * q := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have hdin : d * i ^ n = i ^ n * d := (Commute.pow_right hdi n).eq
          have hi' : d * q * d⁻¹ = i * q := by rw [hi]; group
          calc d ^ (n + 1) * q * (d ^ (n + 1))⁻¹ = d * (d ^ n * q * (d ^ n)⁻¹) * d⁻¹ := by
                rw [pow_succ']
                group
            _ = d * (i ^ n * q) * d⁻¹ := by rw [ih]
            _ = i ^ n * (d * q * d⁻¹) := by
                rw [← mul_assoc, hdin]
                group
            _ = i ^ (n + 1) * q := by rw [hi', pow_succ, mul_assoc]
      have h1 := hpow (orderOf d)
      rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
      have hin : i ^ orderOf d = 1 := right_eq_mul.mp h1
      have hi2 : i ^ 2 = 1 := hIe.2 i hiI
      have hi1 : i = 1 := by
        obtain ⟨m, hm⟩ := hdo
        rw [hm, pow_succ, pow_mul, hi2, one_pow, one_mul] at hin
        exact hin
      have : d * q * d⁻¹ = q := by
        calc d * q * d⁻¹ = d * q * d⁻¹ * q⁻¹ * q := by group
          _ = q := by rw [← hi, hi1, one_mul]
      calc q * d = d * q * d⁻¹ * d := by rw [this]
        _ = d * q := by group
    have hdQ' : d ∈ Q := S.charTwo_J hD (mem_inf.mpr ⟨hdC.1, hdQ⟩)
    obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 J ⟨d, hdQ'⟩
    have hk' : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime (orderOf d) (2 ^ k) :=
      Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hdo)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk'))
  have hD2 : IsPGroup 2 D := by
    intro d
    obtain ⟨a, m, hm, hdm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (d : G)).ne'
    have h1 : (d : G) ^ 2 ^ a ∈ D := pow_mem d.2 _
    have h2 : Odd (orderOf ((d : G) ^ 2 ^ a)) := by
      rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero), hdm,
        Nat.gcd_eq_right (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
      exact hm
    refine ⟨a, Subtype.ext ?_⟩
    simpa using hodd1 _ h1 h2
  have hDQ : D ≤ Q :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans hCsubJ)
      (fun j hj => mem_normalizer_inf (hJC hj) (mem_normalizer_centralizer (hJI hj))) hD2
  apply hg
  rw [S.Lp_eq]
  refine (closure_le _).2 fun x hx => ?_
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  have hxI := hodd x hx.1 hx.2 hx1
  have hx3 : x ^ 3 = 1 := S.odd_pow_three hx.1 hx.2
  have hsign : (F.ρ ⟨x, hxI⟩).sign = 1 := by
    have h1 : F.ρ ⟨x, hxI⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hxI⟩ : ↥(normalizer (I : Set G))) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have h2 := congrArg Equiv.Perm.sign h1
    rw [map_pow, map_one] at h2
    rcases Int.units_eq_one_or (F.ρ ⟨x, hxI⟩).sign with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 (by decide)
  obtain ⟨g, hgK, hgρ⟩ := (F.image_L _).2 hsign
  set c := (g : G)⁻¹ * x with hc
  have hcI : c ∈ centralizer (I : Set G) := by
    refine F.mem_centralizer_of_rho ⟨c, mul_mem (inv_mem g.2) hxI⟩ ?_
    have : (⟨c, mul_mem (inv_mem g.2) hxI⟩ : ↥(normalizer (I : Set G))) = g⁻¹ * ⟨x, hxI⟩ := rfl
    rw [this, map_mul, map_inv, hgρ, inv_mul_cancel]
  have hcC : c ∈ Csub := mul_mem (inv_mem (hKC hgK)) (hLpC hx.1)
  have hcQ : c ∈ Q := hDQ (mem_inf.mpr ⟨hcC, hcI⟩)
  have hxKQ : x ∈ K ⊔ Q := by
    have : x = (g : G) * c := by rw [hc]; group
    rw [this]
    exact mul_mem (mem_sup_left hgK) (mem_sup_right hcQ)
  obtain ⟨m, hm⟩ := pow_two_mem_of_sup ((LieType.BorelTits.pCoreOf_le 2 J).trans hJK)
    (LieType.BorelTits.pCoreOf_isPGroup 2 J) hxKQ
  have hcop : (2 ^ m).gcd (orderOf x) = 1 :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hx.2)
  exact zpowers_le.2 hm (mem_zpowers_pow_iff.2 hcop)

end Set14

end CFSG.Quasithin.H13.U3
