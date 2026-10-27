module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem isPGroup_of_iSup_inf_conj {N R : Subgroup G} (p : ℕ) {A : G → Subgroup G}
    (hA : ∀ h ∈ R, IsPGroup p ↥(A h))
    (hnorm : ∀ n ∈ N, ∀ h ∈ R, ∀ x ∈ A h, n * x * n⁻¹ ∈ A h)
    (hN : N = ⨆ (h : G) (_ : h ∈ R), A h ⊓ N) : IsPGroup p ↥N := by
  have hsub : ∀ h ∈ R, (A h ⊓ N).subgroupOf N ≤ CFSG.pCore p ↥N := by
    intro h hh
    have hI : IsPGroup p ↥(A h ⊓ N) :=
      (hA h hh).of_injective (Subgroup.inclusion (inf_le_left : A h ⊓ N ≤ A h))
        (Subgroup.inclusion_injective _)
    have hJ : IsPGroup p ↥((A h ⊓ N).subgroupOf N) :=
      hI.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : A h ⊓ N ≤ N)).symm
    have hnormal : ((A h ⊓ N).subgroupOf N).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨hnorm g.1 g.2 h hh n hn.1, N.mul_mem (N.mul_mem g.2 hn.2) (N.inv_mem g.2)⟩
    have hmem : (A h ⊓ N).subgroupOf N ∈ {K : Subgroup ↥N | K.Normal ∧ IsPGroup p K} :=
      ⟨hnormal, hJ⟩
    exact le_sSup hmem
  have hNS : N ≤ (CFSG.pCore p ↥N).map N.subtype := by
    refine hN.le.trans (iSup₂_le fun h hh => ?_)
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, hsub h hh (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hcore : ∀ x : ↥N, x ∈ CFSG.pCore p ↥N := by
    intro x
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp (hNS x.2)
    have hkeq : k = x := Subtype.ext hkx
    rw [hkeq] at hk
    exact hk
  exact (CFSG.pCore_isPGroup (p := p) (G := ↥N)).of_surjective (CFSG.pCore p ↥N).subtype
    (fun x => ⟨⟨x, hcore x⟩, rfl⟩)

theorem Ctx.isPGroup_CN_of_311 (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t)
    (hN : hc.CN t = ⨆ (h : G) (_ : h ∈ Rt M (LB M Q B) t),
      conjSubgroup h (LB M Q B) ⊓ hc.CN t) : IsPGroup 2 ↥(hc.CN t) := by
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  have hLB : IsPGroup 2 ↥(LB M Q B) := hc.isPGroup_LB h34 hs.width hs.n_gt hs.noA2 hs.gen
  refine isPGroup_of_iSup_inf_conj (N := hc.CN t) (R := Rt M (LB M Q B) t) 2
    (A := fun h => conjSubgroup h (LB M Q B)) ?_ ?_ hN
  · intro h _
    exact hLB.of_equiv (Subgroup.equivMapOfInjective (LB M Q B) (MulAut.conj h).toMonoidHom
      (MulAut.conj h).injective)
  · intro m hm h hh x hx
    exact (Subgroup.mem_normalizer_iff.mp (hc.CN_normalizes_conj_LB h35 hs.mem hh hm) x).mp hx

theorem Ctx.Nt_le_CN (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) : Nt M (LB M Q B) t ≤ hc.CN t := by
  classical
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  obtain ⟨n', γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  haveI : Finite M₀.E := Module.finite_of_finite (GaloisField 2 n')
  obtain ⟨b, hb0, -, -, -, -⟩ := hc.dictB h
  set R := Rt M (LB M Q B) t with hR
  have hRH : R ≤ H0 M Z := hc.Rt_le_H0 t
  have hPmem : ∀ p ∈ Nt M (LB M Q B) t, ∃ y : ↥R, y ∈ pCore 2 ↥R ∧ (y : G) = p := fun p hp => by
    obtain ⟨y, hy, rfl⟩ := hp
    exact ⟨y, hy, rfl⟩
  have hPR : ∀ p ∈ Nt M (LB M Q B) t, p ∈ R := fun p hp => by
    obtain ⟨y, -, rfl⟩ := hPmem p hp
    exact y.2
  have hPn : ∀ p ∈ Nt M (LB M Q B) t, ∀ l ∈ R, l * p * l⁻¹ ∈ Nt M (LB M Q B) t := by
    intro p hp l hl
    obtain ⟨y, hy, rfl⟩ := hPmem p hp
    exact ⟨⟨l, hl⟩ * y * ⟨l, hl⟩⁻¹, (pCore_normal (p := 2) (G := ↥R)).conj_mem y hy ⟨l, hl⟩, rfl⟩
  have hP2 : ∀ p ∈ Nt M (LB M Q B) t, ∃ k : ℕ, p ^ 2 ^ k = 1 := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := hPmem p hp
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := ↥R)) ⟨y, hy⟩
    refine ⟨k, ?_⟩
    have := congrArg (fun z : pCore 2 ↥R => ((z : ↥R) : G)) hk
    simpa using this
  have hPH : Nt M (LB M Q B) t ≤ H0 M Z := fun p hp => hRH (hPR p hp)
  let Sp : Submodule (GaloisField 2 n') M₀.E :=
    { carrier := {e | ∀ p : G, ∀ hp : p ∈ Nt M (LB M Q B) t, φ ⟨p, hPH hp⟩ e = e}
      add_mem' := fun {a b} ha hb p hp => by rw [map_add, ha p hp, hb p hp]
      zero_mem' := fun p hp => map_zero _
      smul_mem' := fun c e he p hp => by rw [map_smul, he p hp] }
  let Λ : Subgroup (M₀.E ≃ₗ[GaloisField 2 n'] M₀.E) :=
    (φ.comp (Subgroup.inclusion hPH)).range
  have hΛp : IsPGroup 2 Λ := by
    intro g
    obtain ⟨T', p, rfl⟩ := g
    obtain ⟨k, hk⟩ := hP2 p p.2
    refine ⟨k, Subtype.ext ?_⟩
    show ((φ.comp (Subgroup.inclusion hPH)) p) ^ 2 ^ k = 1
    rw [← map_pow]
    have : p ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hTop : (⊤ : Submodule (GaloisField 2 n') M₀.E) ≠ ⊥ := fun hbot => hb0 (by
    have hb : b ∈ (⊤ : Submodule (GaloisField 2 n') M₀.E) := trivial
    rw [hbot] at hb
    exact (Submodule.mem_bot _).mp hb)
  obtain ⟨f, -, hf0, hfix⟩ := exists_fixed_vector_of_isPGroup Λ hΛp ⊤
    (fun _ _ _ _ => trivial) hTop
  have hfSp : f ∈ Sp := fun p hp => hfix _ ⟨⟨p, hp⟩, rfl⟩
  have hSp0 : Sp ≠ ⊥ := fun hbot => hf0 (by
    have hf := hfSp
    rw [hbot] at hf
    exact (Submodule.mem_bot _).mp hf)
  have hSpinv : ∀ l ∈ Rt M (LB M Q B) t, ∀ S : M₀.E ≃ₗ[GaloisField 2 n'] M₀.E,
      (∀ x ∈ Q, M₀.π (l * x * l⁻¹) = S (M₀.π x)) → (∀ e, M₀.Qf (S e) = M₀.Qf e) →
        ∀ v ∈ Sp, S v ∈ Sp := by
    intro l hl S hS _ v hv p hp
    have hlH : l ∈ H0 M Z := hRH hl
    have hSφ : ∀ e, S e = φ ⟨l, hlH⟩ e := fun e =>
      congrFun (eq_of_pi_conj_eq (S₁ := S) (S₂ := φ ⟨l, hlH⟩) hS
        (fun x hx => hφπ ⟨l, hlH⟩ x hx)) e
    rw [hSφ]
    have hp' : l⁻¹ * p * l ∈ Nt M (LB M Q B) t := by
      have := hPn p hp l⁻¹ (R.inv_mem hl)
      simpa using this
    have h1 := hv _ hp'
    have e : (⟨p, hPH hp⟩ : ↥(H0 M Z)) * ⟨l, hlH⟩ = ⟨l, hlH⟩ * ⟨l⁻¹ * p * l, hPH hp'⟩ := by
      apply Subtype.ext
      show p * l = l * (l⁻¹ * p * l)
      group
    calc φ ⟨p, hPH hp⟩ (φ ⟨l, hlH⟩ v) = φ (⟨p, hPH hp⟩ * ⟨l, hlH⟩) v := by rw [map_mul]; rfl
      _ = φ (⟨l, hlH⟩ * ⟨l⁻¹ * p * l, hPH hp'⟩) v := by rw [e]
      _ = φ ⟨l, hlH⟩ (φ ⟨l⁻¹ * p * l, hPH hp'⟩ v) := by rw [map_mul]; rfl
      _ = φ ⟨l, hlH⟩ v := by rw [h1]
  have hinv := hc.img_Vt_le_of_invariant h35 h t Sp hSp0 hSpinv
  intro p hp
  refine Ctx.mem_CN.mpr ⟨hPR p hp, fun v hv => ?_⟩
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  have hπ : M₀.π v ∈ Sp := hinv _ (M₀.pi_mem_img hv hvQ)
  have hfixv := hπ p hp
  have hpvQ : p * v * p⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t (hPR p hp))) v).mp hvQ
  exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hvQ hpvQ).mpr
    (by rw [hφπ ⟨p, hPH hp⟩ v hvQ]; exact hfixv)

theorem Ctx.CN_le_Nt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    (h2 : IsPGroup 2 ↥(hc.CN t)) : hc.CN t ≤ Nt M (LB M Q B) t := by
  set R := Rt M (LB M Q B) t with hR
  have hNR : hc.CN t ≤ R := fun x hx => (Ctx.mem_CN.mp hx).1
  haveI hnorm : ((hc.CN t).subgroupOf R).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hNR).mpr fun x g hx hg => ?_
    have := hc.CN_conj_mem ht hg hx
    simpa using this
  have hp : IsPGroup 2 ↥((hc.CN t).subgroupOf R) :=
    h2.of_injective (Subgroup.subgroupOfEquivOfLe hNR).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hNR).injective
  have hle : (hc.CN t).subgroupOf R ≤ pCore 2 ↥R := le_sSup ⟨hnorm, hp⟩
  intro x hx
  exact ⟨⟨x, hNR hx⟩, hle hx, rfl⟩

end CFSG.RankThree.GF2n.Stroth80
