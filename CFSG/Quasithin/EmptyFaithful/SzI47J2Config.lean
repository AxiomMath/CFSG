module

public import CFSG.Quasithin.EmptyFaithful.SzI47J2Steps
public import CFSG.Quasithin.EmptyFaithful.SzI47J2ConfigCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem j2ConfigOfAlt5_holds : J2ConfigOfAlt5 := by
  intro G _ _ z hcount F R hR hM
  obtain ⟨e⟩ := hM
  have hnW : ∀ r ∈ R, r ≠ 1 → r ∉ F.W := fun r hr hr1 hW => hr1 (by
    have h1 : r ∈ R ⊓ F.W := ⟨hr, hW⟩
    rw [hR.inf_W] at h1
    exact Subgroup.mem_bot.mp h1)
  obtain ⟨y, hyM, hyN, hyR⟩ := SzI47J2C.exists_centralizer_normalizer_of_klein_complement
    (M := F.M hcount) (R := R) (X := F.X) (t := F.t) (fun _ => F.mem_X) (F.M_le_X hcount) e
    hR.comm_M (fun r hr r' hr' => F.comm_of_mem_T (hR.le_T hr) (hR.le_T hr')) hR.X_eq hR.t_mem
    F.t_ne_one hR.card
    (fun r hr hr1 => by
      obtain ⟨k, -, hk⟩ := F.exists_conj_eq_t_of_mem_T (hR.le_T hr) (hnW r hr hr1)
      exact ⟨k⁻¹, by rw [← hk]; group⟩)
    (fun f hf n hn hfn => F.mem_M_of_pow_eq_one hcount hf hn hfn)
  refine ⟨y, ⟨⟨e⟩, F.W_le_M hcount F.z_mem_W, fun r hr => ?_, hR.card, hR.mul_self,
    fun r hr hr1 => F.not_isConj_of_mem_T hcount (hR.le_T hr) (hnW r hr hr1), hyM, hyN, hyR⟩⟩
  rw [Subgroup.mem_centralizer_iff]
  intro m hm
  exact (hR.comm_M r hr m hm).symm

end CFSG.Quasithin
