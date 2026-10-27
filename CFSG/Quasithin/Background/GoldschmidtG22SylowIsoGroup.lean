module

public import CFSG.Quasithin.Background.GoldschmidtG22SylowIsoData
public import CFSG.Quasithin.Background.F6CatG22Psi
public import CFSG.Quasithin.Recognition.M12AmalInst

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open CFSG.QuasithinUnique CFSG.Sporadic.Bridge CFSG.Quasithin.M12Amal

namespace F6

namespace G22SylowIso

theorem nonempty_mulEquiv_of_tables {G H : Type*} [Group G] [Group H] {n : ℕ} (f : Fin n → G)
    (g : Fin n → H) (hf : Function.Bijective f) (hg : Function.Bijective g)
    (σ : Equiv.Perm (Fin n))
    (h : ∀ i j, ∃ l, f i * f j = f l ∧ g (σ i) * g (σ j) = g (σ l)) : Nonempty (G ≃* H) := by
  let E : G ≃ H := (Equiv.ofBijective f hf).symm.trans (σ.trans (Equiv.ofBijective g hg))
  have hE : ∀ i, E (f i) = g (σ i) := fun i => by
    simp only [E, Equiv.trans_apply]
    rw [show (Equiv.ofBijective f hf).symm (f i) = i from
      (Equiv.ofBijective f hf).symm_apply_apply i]
    rfl
  refine ⟨{ toEquiv := E, map_mul' := fun x y => ?_ }⟩
  obtain ⟨i, rfl⟩ := hf.2 x
  obtain ⟨j, rfl⟩ := hf.2 y
  obtain ⟨l, h1, h2⟩ := h i j
  rw [h1]
  change E (f l) = E (f i) * E (f j)
  rw [hE, hE, hE, h2]

section Phi


theorem phi_phi' (x : U33G) : u33Phi' (u33Phi' x) = x := by
  apply u33PresHom_injective
  rw [u33PresHom_phi', u33PresHom_phi', ← mul_assoc, ← mul_assoc, u33Pi_sq, one_mul, mul_assoc,
    u33Pi_sq, mul_one]

end Phi

section Model

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

open G22Perm

include hk2

theorem eqN {l : List ℕ} {g h : G2Group k} (hg : RepL l (psi h2 hk2 g))
    (hh : RepL l (psi h2 hk2 h)) : g = h :=
  psi_injective h2 hk2 (eq_of_repL hg hh)

theorem sEl_mul {i j l : ℕ} (hi : i < 64) (hj : j < 64) (hl : l < 64)
    (h : compL (u33XL i) (u33XL j) = u33XL l) : sEl h2 i * sEl h2 j = sEl h2 l := by
  refine eqN h2 hk2 (l := compL (u33XL i) (u33XL j)) ?_ (by
    rw [h]
    exact repL_psi_sEl h2 hk2 l hl)
  rw [map_mul]
  exact repL_mul (repL_psi_sEl h2 hk2 i hi) (repL_psi_sEl h2 hk2 j hj)

theorem sEl_injective {i j : ℕ} (hi : i < 64) (hj : j < 64) (h : sEl h2 i = sEl h2 j) :
    i = j :=
  u33X_inj i hi j hj (repL_unique (repL_psi_sEl h2 hk2 i hi) (h ▸ repL_psi_sEl h2 hk2 j hj))

@[expose] noncomputable def Ssub : Subgroup (G2Group k) :=
  (g2IndexTwoData h2 hk2).ext u33Data.T u33Phi'_T

theorem Ssub_sylow : IsPGroup 2 (Ssub h2 hk2) ∧ ¬ 2 ∣ (Ssub h2 hk2).index :=
  ⟨(g2IndexTwoData h2 hk2).isPGroup_ext u33Phi'_T u33Extra.syl.1, by
    show ¬ 2 ∣ ((g2IndexTwoData h2 hk2).ext u33Data.T u33Phi'_T).index
    rw [(g2IndexTwoData h2 hk2).index_ext_T u33Phi'_T]
    exact u33Extra.syl.2⟩

theorem mem_Ssub_iff {g : G2Group k} : g ∈ Ssub h2 hk2 ↔ ∃ i < 64, g = sEl h2 i := by
  have D := g2IndexTwoData h2 hk2
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, htg⟩)
    · obtain ⟨j, rfl⟩ := (u33Data.mem_T_iff t).mp ht
      refine ⟨j, by omega, ?_⟩
      simp [sEl, j.2]
      rfl
    · obtain ⟨j, hj⟩ := (u33Data.mem_T_iff (u33Phi' t)).mp (u33Phi'_T t ht)
      refine ⟨j + 32, by omega, ?_⟩
      have hg : g = g2HomC h2 t * g2RhoC h2 := by
        rw [htg, mul_assoc, D.sq, mul_one]
      rw [hg, sEl]
      simp only [show ¬ ((j : ℕ) + 32 < 32) by omega, ↓reduceIte, Nat.add_sub_cancel]
      rw [rho_mul h2 hk2]
      congr 2
      change u33Tel u33GenPG j = _ at hj
      rw [show u33Tel u33GenPG (j : ℕ) = u33Phi' t from hj, phi_phi']
  · rintro ⟨i, hi, rfl⟩
    by_cases hi32 : i < 32
    · refine Or.inl ⟨u33Tel u33GenPG i, ?_, by simp [sEl, hi32]⟩
      exact u33Data.Tel_mem_T ⟨i, hi32⟩
    · refine Or.inr ⟨u33Phi' (u33Tel u33GenPG (i - 32)), u33Phi'_T _
        (u33Data.Tel_mem_T ⟨i - 32, by omega⟩), ?_⟩
      rw [sEl]
      simp only [hi32, ↓reduceIte]
      rw [rho_mul h2 hk2, mul_assoc, D.sq, mul_one]

theorem sEl_mem_Ssub {i : ℕ} (hi : i < 64) : sEl h2 i ∈ Ssub h2 hk2 :=
  (mem_Ssub_iff h2 hk2).mpr ⟨i, hi, rfl⟩

theorem sEl_bijective : Function.Bijective (fun i : Fin 64 =>
    (⟨sEl h2 i, sEl_mem_Ssub h2 hk2 i.2⟩ : ↥(Ssub h2 hk2))) := by
  refine ⟨fun i j h => Fin.ext (sEl_injective h2 hk2 i.2 j.2 (congrArg Subtype.val h)), ?_⟩
  rintro ⟨g, hg⟩
  obtain ⟨i, hi, rfl⟩ := (mem_Ssub_iff h2 hk2).mp hg
  exact ⟨⟨i, hi⟩, rfl⟩

end Model

theorem telG_mul {i j l : ℕ} (hi : i < 64) (hj : j < 64) (hl : l < 64)
    (h : compL (tl i) (tl j) = tl l) : telG i * telG j = telG l :=
  eq_of_reprG (reprG_mul (reprG_tel i hi) (reprG_tel j hj))
    (show ReprG (compL (tl i) (tl j)) (telG l) by rw [h]; exact reprG_tel l hl)

theorem telG_bijective : Function.Bijective (fun i : Fin 64 =>
    (⟨telG i, m12Data.Tel_mem_T i⟩ : ↥m12Data.T)) := by
  refine ⟨fun i j h => tel_inj (congrArg Subtype.val h), ?_⟩
  rintro ⟨g, hg⟩
  obtain ⟨i, hi⟩ := (m12Data.mem_T_iff g).mp hg
  exact ⟨i, Subtype.ext hi⟩

@[expose] def sigPerm : Equiv.Perm (Fin 64) where
  toFun i := ⟨sigAt i, sigAt_lt_chk i i.2⟩
  invFun j := ⟨sigInvAt j, sigInvAt_lt_chk j j.2⟩
  left_inv i := Fin.ext (sigInvAt_sigAt_chk i i.2)
  right_inv j := Fin.ext (sigAt_sigInvAt_chk j j.2)

section Iso

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

open G22Perm

include hk2

theorem S_mulEquiv_T : Nonempty (↥(Ssub h2 hk2) ≃* ↥m12Data.T) := by
  refine nonempty_mulEquiv_of_tables (fun i : Fin 64 =>
    (⟨sEl h2 i, sEl_mem_Ssub h2 hk2 i.2⟩ : ↥(Ssub h2 hk2)))
    (fun i : Fin 64 => (⟨telG i, m12Data.Tel_mem_T i⟩ : ↥m12Data.T))
    (sEl_bijective h2 hk2) telG_bijective sigPerm ?_
  intro i j
  obtain ⟨hl, hS, hT⟩ := hom_chk i i.2 j j.2
  refine ⟨⟨mulIdx i j, hl⟩, Subtype.ext (sEl_mul h2 hk2 i.2 j.2 hl hS), Subtype.ext ?_⟩
  exact telG_mul (sigAt_lt_chk i i.2) (sigAt_lt_chk j j.2) (sigAt_lt_chk _ hl) hT

end Iso

end G22SylowIso

end F6

end CFSG.Quasithin
